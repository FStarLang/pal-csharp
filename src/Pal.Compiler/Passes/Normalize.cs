using System.Collections.Immutable;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Passes;

/// <summary>
/// The Normalize pass: C#-IR → C#-IR rewrites, each defined over C# syntax and applied
/// uniformly to every program (doc/translation.md §0). Its output is still recognisably
/// the source program.
///
/// <list type="bullet">
/// <item>R5.7 — <c>for</c> becomes <c>while</c>.</item>
/// <item>R5.8 — ownership (<c>live</c>) inference for each loop.</item>
/// <item>R5.8b — locals a loop never assigns get their value fixed, not existentialised.</item>
/// <item>R5.9 — the <c>decreases</c> measure every Pulse loop requires (F2).</item>
/// </list>
/// </summary>
public static class Normalize
{
    public static IrProgram Run(IrProgram program, DiagnosticBag diagnostics) =>
        new([.. program.Declarations.Select(d => Declaration(d, diagnostics))]);

    private static IrDecl Declaration(IrDecl decl, DiagnosticBag diagnostics) => decl switch
    {
        // Parameters are in scope throughout the body, so a loop can be live in them —
        // an array parameter written inside a loop is the ordinary case, not an
        // exception.
        IrMethod m when m.Body is not null => m with
        {
            Body = Statement(m.Body, [.. m.Parameters.Select(p => p.Name)], diagnostics),
        },
        _ => decl,
    };

    // -----------------------------------------------------------------------
    // R5.7 / R5.8 / R5.8b / R5.9
    // -----------------------------------------------------------------------

    /// <summary>
    /// R5.5b. C# lets a method return from anywhere; a Pulse block has exactly one
    /// value, its last expression. An <c>if</c> whose branch returns therefore absorbs
    /// the statements that follow it:
    ///
    /// <code>
    ///   if (c) { S1; return e1; }        if (c) { S1; return e1; }
    ///   S2; return e2;             ==&gt;   else   { S2; return e2; }
    /// </code>
    ///
    /// This is a C#-to-C# rewrite that duplicates nothing and reorders nothing: the
    /// statements move into the branch they were already the alternative to. Applied
    /// repeatedly it handles a chain of guard clauses. A <c>return</c> that survives in
    /// a non-final position — from inside a loop, say — is still rejected.
    /// </summary>
    private static ImmutableArray<IrStmt> Returns(ImmutableArray<IrStmt> statements)
    {
        for (var i = 0; i < statements.Length - 1; i++)
        {
            if (statements[i] is not IrIf { Else: null } branch) continue;
            if (!EndsInReturn(branch.Then)) continue;

            var rest = Returns([.. statements.Skip(i + 1)]);
            return
            [
                .. statements.Take(i),
                branch with { Else = new IrBlock(rest[0].Loc, rest) },
            ];
        }
        return statements;
    }

    private static bool EndsInReturn(IrStmt stmt) => stmt switch
    {
        IrReturn => true,
        IrBlock { Statements.IsEmpty: false } b => EndsInReturn(b.Statements[^1]),
        IrIf { Else: not null } i => EndsInReturn(i.Then) && EndsInReturn(i.Else),
        _ => false,
    };

    /// <param name="outer">Locals in scope from enclosing blocks; only these can be live.</param>
    private static IrStmt Statement(IrStmt stmt, ImmutableHashSet<string> outer, DiagnosticBag diagnostics)
    {
        switch (stmt)
        {
            case IrBlock block:
            {
                var scope = outer;
                var result = ImmutableArray.CreateBuilder<IrStmt>();
                foreach (var s in Returns(block.Statements))
                {
                    result.Add(Statement(s, scope, diagnostics));
                    if (s is IrLocalDecl d) scope = scope.Add(d.Name);
                }
                return block with { Statements = result.ToImmutable() };
            }

            case IrIf i:
                return i with
                {
                    Then = Statement(i.Then, outer, diagnostics),
                    Else = i.Else is null ? null : Statement(i.Else, outer, diagnostics),
                };

            case IrWhile w:
                return Loop(w with { Body = Statement(w.Body, outer, diagnostics) }, outer, diagnostics);

            case IrFor f:
                return ForToWhile(f, outer, diagnostics);

            default:
                return stmt;
        }
    }

    /// <summary>
    /// R5.7. <c>for (init; cond; step) body</c> becomes
    /// <c>{ init; while (cond) { body; step } }</c>. The loop specification stays
    /// attached to the loop, and the step is appended after the body — which is exactly
    /// where C# runs it.
    /// </summary>
    private static IrStmt ForToWhile(IrFor f, ImmutableHashSet<string> outer, DiagnosticBag diagnostics)
    {
        var inner = outer;
        foreach (var s in f.Init) if (s is IrLocalDecl d) inner = inner.Add(d.Name);

        var body = Statement(f.Body, inner, diagnostics);
        var merged = new IrBlock(f.Body.Loc, [.. Flatten(body), .. f.Step]);

        var loop = new IrWhile(
            f.Loc,
            f.Cond ?? new IrLiteral(f.Loc, true) { Type = IrPrim.Bool },
            f.Invariants, f.Decreases, merged)
        {
            Counted = DetectCounter(f),
        };

        return new IrBlock(f.Loc, [.. f.Init, Loop(loop, inner, diagnostics)]);
    }

    private static IEnumerable<IrStmt> Flatten(IrStmt s) =>
        s is IrBlock b ? b.Statements : [s];

    /// <summary>
    /// Recognises the shape <c>for (T i = e; i &lt; h; i++)</c> — a counter that a single
    /// step moves monotonically. This is a syntactic property of the loop's own three
    /// clauses; it says nothing about what the loop computes.
    /// </summary>
    private static CountedFor? DetectCounter(IrFor f)
    {
        if (f.Init.Length != 1 || f.Init[0] is not IrLocalDecl decl) return null;
        if (f.Step.Length != 1 || f.Step[0] is not IrAssign
            {
                Target: IrVar target,
                Value: IrBinary { Op: BinOp.Add or BinOp.Sub } step,
            }) return null;
        if (target.Name != decl.Name) return null;
        if (step.Left is not IrVar left || left.Name != decl.Name) return null;
        if (step.Right is not IrLiteral { Value: int k } || k <= 0) return null;

        return new CountedFor(decl.Name, step.Op == BinOp.Add);
    }

    private static IrStmt Loop(IrWhile loop, ImmutableHashSet<string> outer, DiagnosticBag diagnostics)
    {
        var mentioned = new HashSet<string>();
        Free(loop.Cond, mentioned);
        foreach (var i in loop.Invariants) Free(i, mentioned);
        if (loop.Decreases is not null) Free(loop.Decreases, mentioned);
        Free(loop.Body, mentioned);

        var assigned = new HashSet<string>();
        Assigned(loop.Body, assigned);

        // R5.8: ownership of everything the loop touches that it did not itself declare.
        var live = mentioned.Where(outer.Contains).OrderBy(n => n, StringComparer.Ordinal).ToImmutableArray();

        // R5.8b: a local the loop never assigns keeps its value across the loop.
        var unassigned = live.Where(n => !assigned.Contains(n)).ToImmutableArray();

        return loop with
        {
            Live = live,
            Unassigned = unassigned,
            Decreases = loop.Decreases ?? InferMeasure(loop, diagnostics),
        };
    }

    /// <summary>
    /// R5.9. Every Pulse <c>while</c> in a terminating <c>fn</c> needs a measure (F2).
    /// Case 1 (the user's own <c>Pal.Decreases</c>) is handled by the caller; this is
    /// case 2, and case 3 is the diagnostic.
    /// </summary>
    private static IrExpr? InferMeasure(IrWhile loop, DiagnosticBag diagnostics)
    {
        if (loop.Counted is not { } counted)
        {
            diagnostics.Error("PALCS0200", loop.Loc,
                "This loop needs a termination measure. Add `Pal.Decreases(m);` " +
                "as a leading statement of the loop body. pal-csharp does not guess one: " +
                "a guessed measure would be a proof step the translator invented.");
            return null;
        }

        // The counter is a bounded machine integer, so its own type bounds it. Using the
        // type's bound rather than the loop's keeps the measure independent of the guard,
        // which matters because a guard like `i < a.Length` is not a pure expression.
        return new IrTypeBoundMeasure(loop.Loc, counted.Counter, counted.Increasing);
    }

    // -----------------------------------------------------------------------
    // Free variables and assignment targets — both purely syntactic.
    // -----------------------------------------------------------------------

    public static void Free(IrExpr? expr, HashSet<string> into)
    {
        switch (expr)
        {
            case null: return;
            case IrVar v: into.Add(v.Name); return;
            case IrUnary u: Free(u.Operand, into); return;
            case IrBinary b: Free(b.Left, into); Free(b.Right, into); return;
            case IrConditional c: Free(c.Cond, into); Free(c.Then, into); Free(c.Else, into); return;
            case IrElement e: Free(e.Array, into); Free(e.Index, into); return;
            case IrLength l: Free(l.Array, into); return;
            case IrField f: Free(f.Receiver, into); return;
            case IrCall call: foreach (var a in call.Args) Free(a, into); return;
            case IrConvert cv: Free(cv.Operand, into); return;
            case IrOld o: Free(o.Operand, into); return;
            case IrLive lv: Free(lv.Operand, into); return;
            case IrContents ct: Free(ct.Array, into); return;
            case IrSeqOp s: foreach (var a in s.Args) Free(a, into); return;
            case IrQuantifier q:
            {
                var inner = new HashSet<string>();
                Free(q.Body, inner);
                foreach (var b in q.Binders) inner.Remove(b.Name);
                into.UnionWith(inner);
                return;
            }
            default: return;
        }
    }

    public static void Free(IrStmt? stmt, HashSet<string> into)
    {
        switch (stmt)
        {
            case null: return;
            case IrBlock b: foreach (var s in b.Statements) Free(s, into); return;
            case IrLocalDecl d: Free(d.Init, into); return;
            case IrAssign a: Free(a.Target, into); Free(a.Value, into); return;
            case IrIf i: Free(i.Cond, into); Free(i.Then, into); Free(i.Else, into); return;
            case IrWhile w:
                Free(w.Cond, into);
                foreach (var inv in w.Invariants) Free(inv, into);
                Free(w.Decreases, into);
                Free(w.Body, into);
                return;
            case IrFor f:
                foreach (var s in f.Init) Free(s, into);
                Free(f.Cond, into);
                foreach (var s in f.Step) Free(s, into);
                foreach (var inv in f.Invariants) Free(inv, into);
                Free(f.Decreases, into);
                Free(f.Body, into);
                return;
            case IrReturn r: Free(r.Value, into); return;
            case IrExprStmt e: Free(e.Expr, into); return;
            case IrGhostStmt g: Free(g.Prop, into); return;
            default: return;
        }
    }

    /// <summary>
    /// Names a statement assigns. Writing through <c>a[i]</c> counts as assigning
    /// <c>a</c>: the array's contents are what the invariant quantifies over.
    /// </summary>
    public static void Assigned(IrStmt? stmt, HashSet<string> into)
    {
        switch (stmt)
        {
            case null: return;
            case IrBlock b: foreach (var s in b.Statements) Assigned(s, into); return;
            case IrAssign a:
                switch (a.Target)
                {
                    case IrVar v: into.Add(v.Name); break;
                    case IrElement { Array: IrVar arr }: into.Add(arr.Name); break;
                    case IrField { Receiver: IrVar rec }: into.Add(rec.Name); break;
                }
                return;
            case IrIf i: Assigned(i.Then, into); Assigned(i.Else, into); return;
            case IrWhile w: Assigned(w.Body, into); return;
            case IrFor f:
                foreach (var s in f.Init) Assigned(s, into);
                foreach (var s in f.Step) Assigned(s, into);
                Assigned(f.Body, into);
                return;
            case IrExprStmt { Expr: IrCall call }:
                // A method call may write through any array or `ref` argument it is given.
                foreach (var arg in call.Args) if (arg is IrVar v) into.Add(v.Name);
                return;
            default: return;
        }
    }
}
