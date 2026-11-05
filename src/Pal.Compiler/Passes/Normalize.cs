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
/// <item>R5.14 — <c>switch</c> becomes an if/else chain.</item>
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
    ///
    /// A chain of guards is absorbed at its far end: <c>if (c) … else if (d) …</c>, where
    /// both branches return and the chain has no final <c>else</c>, takes what follows as
    /// that <c>else</c>. R5.14's <c>switch</c> is the reason this generality is needed —
    /// a section that ends in <c>return</c> becomes exactly such a chain — but the shape
    /// is one a hand-written program can have too.
    /// </summary>
    private static ImmutableArray<IrStmt> Returns(ImmutableArray<IrStmt> statements)
    {
        for (var i = 0; i < statements.Length - 1; i++)
        {
            if (statements[i] is not IrIf branch || !GuardChain(branch)) continue;

            var rest = Returns([.. statements.Skip(i + 1)]);
            return
            [
                .. statements.Take(i),
                Attach(branch, new IrBlock(rest[0].Loc, rest)),
            ];
        }
        return statements;
    }

    /// <summary>
    /// A chain <c>if (c1) T1 else if (c2) T2 …</c> that ends without an <c>else</c> and
    /// whose every branch returns. Such a chain has one exit that is not a return — the
    /// one the missing <c>else</c> stands for — and that is where the tail belongs.
    /// </summary>
    private static bool GuardChain(IrIf i) =>
        EndsInReturn(i.Then) && (i.Else is null || (i.Else is IrIf next && GuardChain(next)));

    private static IrIf Attach(IrIf chain, IrStmt tail) =>
        chain.Else is IrIf next
            ? chain with { Else = Attach(next, tail) }
            : chain with { Else = tail };

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
                    var normalized = Statement(s, scope, diagnostics);
                    // R5.14's expansion is spliced, not nested: its chain has to be a
                    // statement of *this* block for R5.5b below to absorb what follows it.
                    if (s is IrSwitch sw)
                    {
                        result.AddRange(Flatten(normalized));
                        scope = scope.Add(sw.Scrutinee.Name);
                    }
                    else result.Add(normalized);
                    if (s is IrLocalDecl d) scope = scope.Add(d.Name);
                }
                // Again, because R5.14 turns a `switch` into an `if` chain and a section
                // that ended in `return` is a guard clause that was not one before.
                return block with { Statements = Returns(result.ToImmutable()) };
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

            case IrSwitch s:
                return SwitchToIf(s, outer, diagnostics);

            case IrTry t:
                return Try(t with
                {
                    Body = (IrBlock)Statement(t.Body, outer, diagnostics),
                    Catches = [.. t.Catches.Select(c => c with
                    {
                        Body = (IrBlock)Statement(
                            c.Body, c.Var is null ? outer : outer.Add(c.Var), diagnostics),
                    })],
                }, outer);

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

        // A `continue` must still run the step, so a body that contains one keeps the
        // step in its own slot; otherwise the two are indistinguishable and appending is
        // both simpler and identical in meaning. The question is asked of the *normalized*
        // body: R5.14's `continue` is inside an `IrSwitch` until the rewrite has run, and
        // a traversal that stopped there would report a body that never escapes.
        var loop = Escapes(body)
            ? new IrWhile(
                f.Loc,
                f.Cond ?? new IrLiteral(f.Loc, true) { Type = IrPrim.Bool },
                f.Invariants, f.Decreases, body)
            {
                Counted = DetectCounter(f),
                Step = f.Step,
            }
            : new IrWhile(
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
    /// R5.14. <c>switch (t) { case k1: case k2: S1 break; … default: Sd break; }</c>
    /// becomes <c>if (t == k1 || t == k2) { S1 } else if … else { Sd }</c>.
    ///
    /// The scrutinee is already an immutable local (the frontend bound it), so testing it
    /// once per arm evaluates the governing expression exactly as often as C# does: once.
    /// The <c>default</c> section moves to the end whatever its written position, which is
    /// sound because C# requires the case labels to be distinct constants — no two arms
    /// can both be taken, so their order carries nothing. A <c>switch</c> with no
    /// <c>default</c> gets no final <c>else</c>, which is C#'s fallthrough to nothing.
    /// </summary>
    private static IrStmt SwitchToIf(IrSwitch s, ImmutableHashSet<string> outer, DiagnosticBag diagnostics)
    {
        var arms = s.Sections.Where(sec => !sec.Labels.IsEmpty).ToList();
        var fallback = s.Sections.FirstOrDefault(sec => sec.Labels.IsEmpty);

        var scrutinee = new IrVar(s.Scrutinee.Loc, s.Scrutinee.Name) { Type = s.Scrutinee.Type };

        IrStmt? chain = fallback is null ? null : Body(fallback);
        for (var i = arms.Count - 1; i >= 0; i--)
            chain = new IrIf(arms[i].Loc, Test(scrutinee, arms[i]), Body(arms[i]), chain);

        var expansion = chain is null
            ? ImmutableArray.Create<IrStmt>(s.Scrutinee)
            : [s.Scrutinee, Statement(chain, outer.Add(s.Scrutinee.Name), diagnostics)];
        return new IrBlock(s.Loc, expansion);

        static IrStmt Body(IrSwitchSection section) => new IrBlock(section.Loc, section.Statements);
    }

    /// <summary>The disjunction of a section's labels: stacked labels are alternatives.</summary>
    private static IrExpr Test(IrExpr scrutinee, IrSwitchSection section) =>
        section.Labels
            .Select(k => (IrExpr)new IrBinary(k.Loc, BinOp.Eq, scrutinee, k) { Type = IrPrim.Bool })
            .Aggregate((a, b) => new IrBinary(b.Loc, BinOp.Or, a, b) { Type = IrPrim.Bool });

    /// <summary>
    /// Recognises the shape <c>for (T i = e; i &lt; h; i++)</c> — a counter that a single
    /// step moves monotonically. This is a syntactic property of the loop's own three
    /// clauses; it says nothing about what the loop computes.
    /// </summary>
    /// <summary>Whether a loop body contains a `break` or `continue` of its own.</summary>
    private static bool Escapes(IrStmt stmt) => stmt switch
    {
        IrBreak or IrContinue => true,
        IrBlock b => b.Statements.Any(Escapes),
        IrIf i => Escapes(i.Then) || (i.Else is not null && Escapes(i.Else)),
        _ => false,
    };

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
        foreach (var st in loop.Step) Free(st, mentioned);

        var assigned = new HashSet<string>();
        Assigned(loop.Body, assigned);
        foreach (var st in loop.Step) Assigned(st, assigned);

        // R4.11, inside a loop. `Assigned` answers "which names need a cell", and answers
        // it by assuming a call writes everything it is handed. For an object that is
        // ruinous rather than merely conservative: the loop would re-quantify its model on
        // every turn, so a method whose postcondition names the model it was *given* could
        // not prove it after the loop, and the shape a client passed in would come back
        // anonymous. `Mutated` is the precise rule, and it is used only for objects.
        var mutated = new HashSet<string>();
        Mutated(loop.Body, mutated);
        foreach (var st in loop.Step) Mutated(st, mutated);
        var objects = Objects(loop);

        // R5.8: ownership of everything the loop touches that it did not itself declare.
        var live = mentioned.Where(outer.Contains).OrderBy(n => n, StringComparer.Ordinal).ToImmutableArray();

        // R5.8b: a local the loop never assigns keeps its value across the loop.
        var unassigned = live
            .Where(n => objects.Contains(n) ? !mutated.Contains(n) : !assigned.Contains(n))
            .ToImmutableArray();

        return loop with
        {
            Live = live,
            Unassigned = unassigned,
            Decreases = loop.Decreases ?? InferMeasure(loop, diagnostics),
        };
    }

    /// <summary>
    /// R19.4. A try owns everything in scope (F86), and keeps the value of what neither
    /// its body nor a handler assigns. As for a loop (R5.8b), an object counts as assigned
    /// only if it is <see cref="Mutated"/>.
    /// </summary>
    private static IrTry Try(IrTry t, ImmutableHashSet<string> outer)
    {
        var assigned = new HashSet<string>();
        var mutated = new HashSet<string>();
        Assigned(t, assigned);
        Mutated(t, mutated);
        var objects = new HashSet<string>(
            Check.Statements(t).SelectMany(Check.Expressions).SelectMany(Check.Subexpressions)
                .OfType<IrVar>().Where(v => v.Type is IrClassType).Select(v => v.Name));
        var live = outer.OrderBy(n => n, StringComparer.Ordinal).ToImmutableArray();
        return t with
        {
            Live = live,
            Unassigned = [.. live.Where(n =>
                objects.Contains(n) ? !mutated.Contains(n) : !assigned.Contains(n))],
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
            case IrNew n: foreach (var f in n.Fields) Free(f.Value, into); return;
            case IrRefArg r: Free(r.Operand, into); return;
            case IrCall call: foreach (var a in call.Args) Free(a, into); return;
            case IrConvert cv: Free(cv.Operand, into); return;
            case IrStmtExpr se: foreach (var s in se.Prelude) Free(s, into); Free(se.Value, into); return;
            case IrOld o: Free(o.Operand, into); return;
            case IrLive lv: Free(lv.Operand, into); return;
            case IrNewArray na: Free(na.Length, into); if (na.Source is { } nas) Free(nas, into); return;
            case IrArraySearch se: Free(se.Array, into); Free(se.Item, into); Free(se.Start, into); Free(se.Count, into); return;
            case IrContents ct: Free(ct.Array, into); return;
            case IrSeqOp s: foreach (var a in s.Args) Free(a, into); return;
            case IrListOp lo: foreach (var a in lo.Args) Free(a, into); return;
            case IrSpecOp so: foreach (var a in so.Args) Free(a, into); return;
            case IrOptionOp oo: Free(oo.Operand, into); return;
            case IrRaise ra: Free(ra.Exception, into); return;
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
                foreach (var st in w.Step) Free(st, into);
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
            case IrArrayOp c: foreach (var a in c.Args) Free(a, into); return;
            case IrGhostStmt g: Free(g.Prop, into); return;
            case IrThrow th: Free(th.Value, into); return;
            case IrTry t:
                foreach (var inv in t.Invariants) Free(inv, into);
                Free(t.Body, into);
                foreach (var c in t.Catches) { Free(c.When, into); Free(c.Body, into); }
                return;
            default: return;
        }
    }

    /// <summary>
    /// Names a statement assigns. Writing through <c>a[i]</c> counts as assigning
    /// <c>a</c>: the array's contents are what the invariant quantifies over.
    /// </summary>
    /// <summary>The object-typed names a loop mentions.</summary>
    private static HashSet<string> Objects(IrWhile loop) =>
        [.. Check.Statements(loop.Body).Concat(loop.Step)
                .SelectMany(Check.Expressions)
                .Concat(loop.Invariants)
                .Append(loop.Cond)
                .SelectMany(Check.Subexpressions)
                .OfType<IrVar>()
                .Where(v => v.Type is IrClassType)
                .Select(v => v.Name)];

    /// <summary>
    /// R4.11. The names whose model a statement may move: an assignment target, a name
    /// passed by reference, and anything handed to a callee — except the receiver of an
    /// instance method the frontend has already found read-only, whose own postcondition
    /// says its model did not move.
    ///
    /// <para>This is the one place that rule is written. <see cref="Assigned"/> answers a
    /// different question (R4.2: which names need a mutable cell) and may safely
    /// over-approximate; this one may not, because an object wrongly called mutable loses
    /// its model to an existential and takes the caller's reasoning with it.</para>
    /// </summary>
    public static void Mutated(IrStmt? stmt, HashSet<string> into)
    {
        switch (stmt)
        {
            case null: return;
            case IrBlock b: foreach (var x in b.Statements) Mutated(x, into); return;
            case IrLocalDecl d: MutatedIn(d.Init, into); return;
            case IrAssign a:
                switch (a.Target)
                {
                    case IrVar v: into.Add(v.Name); break;
                    case IrElement { Array: IrVar arr }: into.Add(arr.Name); break;
                    case IrField { Receiver: IrVar rec }: into.Add(rec.Name); break;
                }
                MutatedIn(a.Target, into);
                MutatedIn(a.Value, into);
                return;
            case IrIf i:
                MutatedIn(i.Cond, into);
                Mutated(i.Then, into);
                Mutated(i.Else, into);
                return;
            case IrWhile w:
                MutatedIn(w.Cond, into);
                Mutated(w.Body, into);
                foreach (var st in w.Step) Mutated(st, into);
                return;
            case IrFor f:
                foreach (var st in f.Init.Concat(f.Step)) Mutated(st, into);
                Mutated(f.Body, into);
                return;
            case IrReturn r: MutatedIn(r.Value, into); return;
            case IrExprStmt e: MutatedIn(e.Expr, into); return;
            case IrArrayOp c:
                if (c.Written is IrVar dv) into.Add(dv.Name);
                else if (c.Written is IrField { Receiver: IrVar dr }) into.Add(dr.Name);
                foreach (var a in c.Args) MutatedIn(a, into);
                return;
            case IrThrow th: MutatedIn(th.Value, into); return;
            case IrTry t:
                Mutated(t.Body, into);
                foreach (var c in t.Catches) { MutatedIn(c.When, into); Mutated(c.Body, into); }
                return;
            default: return;
        }
    }

    private static void MutatedIn(IrExpr? expr, HashSet<string> into)
    {
        switch (expr)
        {
            case null: return;
            case IrCall c:
                for (var i = 0; i < c.Args.Length; i++)
                {
                    var readOnlyReceiver = i == 0 && c.HasReceiver && !c.MutatesReceiver;
                    switch (c.Args[i])
                    {
                        case IrVar v when !readOnlyReceiver: into.Add(v.Name); break;
                        case IrRefArg { Operand: IrVar rv }: into.Add(rv.Name); break;
                    }
                    MutatedIn(c.Args[i], into);
                }
                return;
            case IrUnary u: MutatedIn(u.Operand, into); return;
            case IrBinary b: MutatedIn(b.Left, into); MutatedIn(b.Right, into); return;
            case IrConditional c2:
                MutatedIn(c2.Cond, into);
                MutatedIn(c2.Then, into);
                MutatedIn(c2.Else, into);
                return;
            case IrConvert cv: MutatedIn(cv.Operand, into); return;
            case IrStmtExpr se: foreach (var s in se.Prelude) Mutated(s, into); MutatedIn(se.Value, into); return;
            case IrRefArg ra: MutatedIn(ra.Operand, into); return;
            case IrElement el: MutatedIn(el.Array, into); MutatedIn(el.Index, into); return;
            case IrField f: MutatedIn(f.Receiver, into); return;
            default: return;
        }
    }

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
                // R23.9. The target's index is evaluated too, and may write: `a[--i] = x`.
                if (a.Target is IrElement target) AssignedByCalls(target.Index, into);
                AssignedByCalls(a.Value, into);
                return;
            case IrIf i:
                AssignedByCalls(i.Cond, into);
                Assigned(i.Then, into);
                Assigned(i.Else, into);
                return;
            case IrWhile w:
                AssignedByCalls(w.Cond, into);
                Assigned(w.Body, into);
                foreach (var st in w.Step) Assigned(st, into);
                return;
            case IrFor f:
                foreach (var s in f.Init) Assigned(s, into);
                foreach (var s in f.Step) Assigned(s, into);
                Assigned(f.Body, into);
                return;
            case IrLocalDecl d: AssignedByCalls(d.Init, into); return;
            case IrReturn r: AssignedByCalls(r.Value, into); return;
            case IrExprStmt e: AssignedByCalls(e.Expr, into); return;
            case IrThrow th: AssignedByCalls(th.Value, into); return;
            case IrTry t:
                Assigned(t.Body, into);
                foreach (var c in t.Catches) { AssignedByCalls(c.When, into); Assigned(c.Body, into); }
                return;
            default: return;
        }
    }

    /// <summary>
    /// Names written by the calls occurring anywhere in an expression. A callee may
    /// write through any array it is handed and through every by-reference argument, so
    /// those names must be existentially quantified in an enclosing loop's invariant —
    /// otherwise the invariant would silently assert that the call changed nothing.
    /// </summary>
    private static void AssignedByCalls(IrExpr? expr, HashSet<string> into)
    {
        switch (expr)
        {
            case null: return;
            case IrCall call:
                foreach (var arg in call.Args)
                {
                    switch (arg)
                    {
                        case IrVar v: into.Add(v.Name); break;
                        case IrRefArg { Operand: IrVar rv }: into.Add(rv.Name); break;
                    }
                    AssignedByCalls(arg, into);
                }
                return;
            case IrRefArg r: AssignedByCalls(r.Operand, into); return;
            case IrUnary u: AssignedByCalls(u.Operand, into); return;
            case IrBinary b: AssignedByCalls(b.Left, into); AssignedByCalls(b.Right, into); return;
            case IrConditional c:
                AssignedByCalls(c.Cond, into);
                AssignedByCalls(c.Then, into);
                AssignedByCalls(c.Else, into);
                return;
            case IrElement el: AssignedByCalls(el.Array, into); AssignedByCalls(el.Index, into); return;
            case IrField f: AssignedByCalls(f.Receiver, into); return;
            case IrConvert cv: AssignedByCalls(cv.Operand, into); return;
            // R13.3. An expression can now perform a write, so the question "what does
            // this statement assign" is no longer answered by looking at statements
            // alone.
            case IrStmtExpr se:
                foreach (var s in se.Prelude) Assigned(s, into);
                AssignedByCalls(se.Value, into);
                return;
            case IrNew n: foreach (var f in n.Fields) AssignedByCalls(f.Value, into); return;
            default: return;
        }
    }
}
