using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Lowers C# statements to <see cref="IrStmt"/>, structure for structure
/// (doc/translation.md §5). Loops stay loops, both branches of an <c>if</c> survive,
/// and statement order is preserved exactly.
/// </summary>
public sealed class StmtLowerer(
    SemanticModel model,
    WellKnown known,
    DiagnosticBag diagnostics,
    ImmutableHashSet<string>? objectFields = null,
    BorrowContext? borrow = null)
{
    private readonly ExprLowerer _code =
        new(model, known, diagnostics, specPosition: false) { ObjectFields = objectFields ?? [], Borrow = borrow };
    private readonly ExprLowerer _spec =
        new(model, known, diagnostics, specPosition: true)
        {
            ObjectFields = objectFields ?? [], Borrow = borrow, BorrowBody = borrow is not null,
        };

    /// <summary>
    /// R4.12c. A constructor initializer is an expression that is not inside any statement,
    /// so the one caller that needs it reaches the expression lowerer directly.
    /// </summary>
    public ExprLowerer Expressions => _code;

    /// <summary>R14.2a. The type parameters either lowerer took a <c>default</c> at.</summary>
    public bool Defaulted(string typeParameter) =>
        _code.DefaultedTypeParameters.Contains(typeParameter) ||
        _spec.DefaultedTypeParameters.Contains(typeParameter);

    public IrStmt Lower(StatementSyntax node)
    {
        var loc = Locations.From(node);
        return node switch
        {
            BlockSyntax b => LowerBlock(b),
            LocalDeclarationStatementSyntax d => LowerLocalDeclaration(d, loc),
            ExpressionStatementSyntax e => LowerExpressionStatement(e, loc),
            IfStatementSyntax i when RegionPatternIf(i, loc) is { } bound => bound,
            // R33.9. `out var x` in an `if`'s condition: as R27.43's loop, declared ahead.
            IfStatementSyntax i when OutDeclarations(i.Condition, loc) is { IsEmpty: false } outs =>
                new IrBlock(loc, [.. outs, new IrIf(loc, _code.Lower(i.Condition),
                    Lower(i.Statement), i.Else is null ? null : Lower(i.Else.Statement))]) { Splice = true },
            IfStatementSyntax i => new IrIf(loc, _code.Lower(i.Condition),
                Lower(i.Statement), i.Else is null ? null : Lower(i.Else.Statement)),
            WhileStatementSyntax w when OutDeclarations(w.Condition, loc) is { IsEmpty: false } outs =>
                new IrBlock(loc, [.. outs, LowerWhile(w, loc)]) { Splice = true },
            WhileStatementSyntax w => LowerWhile(w, loc),
            DoStatementSyntax d => LowerDo(d, loc),
            ForStatementSyntax f => LowerFor(f, loc),
            ForEachStatementSyntax f => LowerForEach(f, loc),
            ReturnStatementSyntax r when _loopDepth > 0 => LowerReturnInLoop(r, loc),
            ReturnStatementSyntax r => new IrReturn(loc,
                r.Expression is null ? null : Returned(r, ReturnedType(r))),
            BreakStatementSyntax => new IrBreak(loc),
            ContinueStatementSyntax => new IrContinue(loc),
            SwitchStatementSyntax s => LowerSwitch(s, loc),
            GotoStatementSyntax g => LowerGoto(g, loc),
            LabeledStatementSyntax l => Lower(l.Statement),
            EmptyStatementSyntax => new IrBlock(loc, []),
            YieldStatementSyntax y => LowerYield(y, loc),
            ThrowStatementSyntax t => new IrThrow(loc,
                t.Expression is null ? null : _code.Lower(t.Expression)),
            TryStatementSyntax t => LowerTry(t, loc),
            _ => UnsupportedStatement(node, loc),
        };
    }

    /// <summary>
    /// R19.4. <c>try { … } catch (E e) when (…) { … }</c>. A <c>finally</c> is refused:
    /// it runs on every exit, including <c>return</c>, and Pulse's <c>try</c> has no such
    /// clause.
    /// </summary>
    private IrStmt LowerTry(TryStatementSyntax node, IrLoc loc)
    {
        if (node.Finally is not null)
        {
            diagnostics.Error("PALCS0614", Locations.From(node.Finally.FinallyKeyword),
                "A `finally` clause. Pulse's `try` has handlers but no clause that runs on every " +
                "exit; restructure the code so the cleanup is in the try's tail and in each " +
                "handler (doc/translation.md R19.4).");
            return new IrBlock(loc, []);
        }

        var catches = ImmutableArray.CreateBuilder<IrCatch>();
        foreach (var c in node.Catches)
        {
            var cloc = Locations.From(c.CatchKeyword);
            IrExnType type = new(null);
            string? name = null;
            if (c.Declaration is { } d)
            {
                var t = model.GetTypeInfo(d.Type).Type;
                if (known.MapType(t) is not IrExnType mapped)
                {
                    diagnostics.Error("PALCS0614", Locations.From(d.Type),
                        $"A handler for `{t}`. Only `System.Exception` and the exception classes " +
                        "the program declares can be caught (doc/translation.md R19.4).");
                    continue;
                }
                type = mapped;
                if (d.Identifier.ValueText is { Length: > 0 } id) name = id;
            }
            var when = c.Filter is { } f ? _code.Lower(f.FilterExpression) : null;
            catches.Add(new IrCatch(cloc, type, name, when, LowerBlock(c.Block)));
        }
        // R19.5. A try states its invariant the way a loop does, at the head of its body.
        var (invariants, decreases, body) = ExtractLoopSpecs(node.Block, loop: false);
        if (decreases is not null)
            diagnostics.Error("PALCS0614", decreases.Loc,
                "`Pal.Decreases` in a `try`. A `try` runs its body once; only a loop has a " +
                "measure (doc/translation.md R19.5).");
        return new IrTry(loc, (IrBlock)body, catches.ToImmutable()) { Invariants = invariants };
    }

    private IrStmt UnsupportedStatement(SyntaxNode node, IrLoc loc)
    {
        diagnostics.Unsupported(loc, $"The statement `{node.Kind()}`");
        return new IrBlock(loc, []);
    }

    /// <summary>
    /// R5.14. `goto case` and `goto default` are C#'s way of asking for the fallthrough
    /// the language otherwise forbids, and they are the reason PAL — translating C, where
    /// fallthrough is implicit — needs a `hit` flag threaded through its whole desugaring.
    /// pal-csharp needs no such flag, because C# has already ruled out the case that
    /// requires one, and these two statements are the exception it left open.
    /// </summary>
    private IrStmt LowerGoto(GotoStatementSyntax node, IrLoc loc)
    {
        var jump = node.Kind() switch
        {
            SyntaxKind.GotoCaseStatement => "`goto case`",
            SyntaxKind.GotoDefaultStatement => "`goto default`",
            _ => null,
        };
        if (node.IsKind(SyntaxKind.GotoStatement)) return LowerForwardGoto(node, loc);
        if (jump is null) return UnsupportedStatement(node, loc);

        diagnostics.Unsupported(loc, $"A {jump} statement",
            "It re-introduces the fallthrough C# otherwise forbids, and an if/else chain " +
            "(R5.14) has no way to enter one arm from another. Where the target section " +
            "is to run *instead*, write its labels on this section as well; where it is " +
            "to run *as well*, lift the shared work into a method both sections call.");
        return new IrBlock(loc, []);
    }

    /// <summary>
    /// R33.2. <c>goto L;</c> to a label later in the method's outermost block is the code
    /// from <c>L</c> to the end of that block, copied to the jump. That code must end by
    /// leaving the method (its end point is unreachable), so it never falls back into
    /// what follows the jump; and a label whose block position is reachable only by
    /// jumps is not lowered where it stands (<see cref="LowerStatements"/>).
    /// </summary>
    private IrStmt LowerForwardGoto(GotoStatementSyntax node, IrLoc loc)
    {
        var name = (node.Expression as IdentifierNameSyntax)?.Identifier.ValueText;
        var body = node.Ancestors().Select(a => a switch
        {
            BaseMethodDeclarationSyntax m => m.Body,
            AccessorDeclarationSyntax a2 => a2.Body,
            _ => null,
        }).FirstOrDefault(b => b is not null);
        var statements = body?.Statements ?? default;
        var at = body is null ? -1 : statements.IndexOf(st => st is LabeledStatementSyntax l && l.Identifier.ValueText == name);
        // R30.29. A jump back to a label is followed as one forward is, so long as the code it
        // copies does not contain the jump.
        string? why =
            at < 0 ? "its label is not a statement of the method's outermost block"
            : _expanding.Contains(name!) ? "it jumps back into the code it is part of"
            : node.Ancestors().TakeWhile(a => a != body).Any(a => a is TryStatementSyntax or
                AnonymousFunctionExpressionSyntax or LocalFunctionStatementSyntax)
                ? "it leaves a `try`, a lambda or a local function"
            : model.AnalyzeControlFlow(statements[^1]) is { Succeeded: true, EndPointIsReachable: false }
                ? null : "the code from its label on can run off the end of the method";
        if (why is not null)
        {
            diagnostics.Unsupported(loc, "A `goto` statement",
                $"Only a forward jump to a label of the method's outermost block, whose code " +
                $"then leaves the method, is translated (doc/translation.md R33.2); {why}.");
            return new IrBlock(loc, []);
        }
        // A local of the outermost block declared between the jump and its label is in scope
        // at the label but not yet declared here; C#'s definite assignment makes the code
        // from the label assign it before reading it.
        var from = statements.IndexOf(st => st.Span.Contains(node.Span));
        var tail = statements.Skip(at).ToList();
        var declared = ImmutableArray.CreateBuilder<IrStmt>();
        // R30.29. So may one under a label.
        static StatementSyntax Unlabeled(StatementSyntax st) => st is LabeledStatementSyntax l ? Unlabeled(l.Statement) : st;
        foreach (var st in statements.Skip(from + 1).Take(Math.Max(0, at - from - 1)).Select(Unlabeled)
                     .OfType<LocalDeclarationStatementSyntax>())
            foreach (var v in st.Declaration.Variables)
                if (model.GetDeclaredSymbol(v) is ILocalSymbol local &&
                    tail.Any(t => t.DescendantNodes().OfType<IdentifierNameSyntax>().Any(id =>
                        SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(id).Symbol, local))) &&
                    known.MapType(local.Type) is { } localType)
                {
                    // R30.29. A snapshot local starts as the null reference.
                    if (local.IsRef && RefSnapshots.Enclosing(node, model) is not null)
                    {
                        var optionType = new IrOptionType(localType);
                        declared.Add(new IrLocalDecl(Locations.From(v), v.Identifier.ValueText, optionType,
                            new IrNull(Locations.From(v)) { Type = optionType }));
                        RegisterSnapshot(local, optionType, Locations.From(v));
                        continue;
                    }
                    declared.Add(new IrLocalDecl(Locations.From(v), v.Identifier.ValueText, localType, null));
                }
        _expanding.Add(name!);
        try { return new IrBlock(loc, [.. declared, .. LowerStatements(tail)]); }
        finally { _expanding.Remove(name!); }
    }

    /// <summary>R30.29. The labels whose code is being copied to a jump.</summary>
    private readonly HashSet<string> _expanding = [];

    /// <summary>
    /// R33.2. Whether control can reach the end of <paramref name="statement"/>: C#'s
    /// reachability, except that a call of a <c>[DoesNotReturn]</c> method does not return.
    /// </summary>
    private bool FallsThrough(StatementSyntax statement) =>
        statement is LabeledStatementSyntax labeled ? FallsThrough(labeled.Statement) :
        model.AnalyzeControlFlow(statement) is not { Succeeded: true, EndPointIsReachable: false } &&
        !(statement is ExpressionStatementSyntax { Expression: InvocationExpressionSyntax call } &&
          model.GetSymbolInfo(call).Symbol is IMethodSymbol callee &&
          callee.GetAttributes().Any(a => a.AttributeClass?.Name == "DoesNotReturnAttribute"));

    private IrBlock LowerBlock(BlockSyntax block) =>
        new(Locations.From(block), LowerStatements([.. ReachableStatements(block.Statements)]));

    private ImmutableArray<IrStmt> LowerStatements(IReadOnlyList<StatementSyntax> statements)
    {
        var lowered = ImmutableArray.CreateBuilder<IrStmt>();
        for (var i = 0; i < statements.Count; i++)
        {
            // R33.2. A label the statement before it cannot fall into is reached only by
            // `goto`, each of which has a copy of what follows.
            if (i > 0 && statements[i] is LabeledStatementSyntax && !FallsThrough(statements[i - 1]))
                break;
            if (HeldChoice(statements[i]) is var (x, cond, a, b))
            {
                var rest = statements.Skip(i + 1).ToList();
                var loc = Locations.From(statements[i]);
                lowered.Add(new IrIf(loc, _code.Lower(cond),
                    new IrBlock(loc, Aliased(x, a, () => LowerStatements(rest))),
                    new IrBlock(loc, Aliased(x, b, () => LowerStatements(rest)))));
                break;
            }
            var s = Lower(statements[i]);
            if (s is IrBlock { Splice: true } spliced) lowered.AddRange(spliced.Statements);
            else lowered.Add(s);
        }
        return lowered.ToImmutable();
    }

    /// <summary>
    /// R27.54. <c>S x = c ? a : b;</c>, where <c>a</c> and <c>b</c> are locals holding
    /// borrowing structs (R27.41) that nothing after the declaration names: the rest of the
    /// block runs once with <c>x</c> another name for <c>a</c> and once for <c>b</c>, under
    /// <c>if (c)</c>. <c>x</c> is a copy of the chosen struct, but as the original is never
    /// read again, updating the original in place is indistinguishable.
    /// </summary>
    private (ILocalSymbol X, ExpressionSyntax Cond, ILocalSymbol A, ILocalSymbol B)? HeldChoice(StatementSyntax statement)
    {
        if (statement is not LocalDeclarationStatementSyntax
            {
                Declaration.Variables: [{ Initializer.Value: var init } v]
            } decl ||
            Unparenthesized(init) is not ConditionalExpressionSyntax cond ||
            model.GetDeclaredSymbol(v) is not ILocalSymbol { RefKind: RefKind.None } x ||
            x.Type is not INamedTypeSymbol { TypeKind: TypeKind.Struct } st || !Borrowing.IsBorrowing(st, known) ||
            model.GetSymbolInfo(Unparenthesized(cond.WhenTrue)).Symbol is not ILocalSymbol a ||
            model.GetSymbolInfo(Unparenthesized(cond.WhenFalse)).Symbol is not ILocalSymbol b ||
            !_code.Holds(a) || !_code.Holds(b))
            return null;
        var body = decl.Ancestors().FirstOrDefault(n => n is BaseMethodDeclarationSyntax or AccessorDeclarationSyntax) ?? decl.Parent!;
        var later = body.DescendantNodes().OfType<IdentifierNameSyntax>()
            .Where(n => n.SpanStart > decl.Span.End)
            .Select(n => model.GetSymbolInfo(n).Symbol);
        if (later.Any(sym => SymbolEqualityComparer.Default.Equals(sym, a) || SymbolEqualityComparer.Default.Equals(sym, b)))
            return null;
        var written = body.DescendantNodes().OfType<AssignmentExpressionSyntax>()
            .Any(w => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(w.Left).Symbol, x));
        return written ? null : (x, cond.Condition, a, b);
    }

    private static ExpressionSyntax Unparenthesized(ExpressionSyntax e) =>
        e is ParenthesizedExpressionSyntax p ? Unparenthesized(p.Expression) : e;

    private T Aliased<T>(ILocalSymbol x, ILocalSymbol target, Func<T> f)
    {
        _code.Alias(x, target);
        _spec.Alias(x, target);
        try { return f(); }
        finally { _code.Unalias(x); _spec.Unalias(x); }
    }

    /// <summary>
    /// R27.48. The statements of a block up to and including a <c>Pal.Unreachable()</c>.
    /// What follows it is never lowered: that the point is never reached is proved there.
    /// </summary>
    private IEnumerable<StatementSyntax> ReachableStatements(IEnumerable<StatementSyntax> statements)
    {
        foreach (var s in statements)
        {
            yield return s;
            if (s is ExpressionStatementSyntax { Expression: InvocationExpressionSyntax call } &&
                model.GetSymbolInfo(call).Symbol is IMethodSymbol { Name: nameof(PalLang.Pal.Unreachable) } m &&
                known.IsPalIntrinsic(m))
                yield break;
        }
    }

    // -----------------------------------------------------------------------
    // R26.2. `return` inside a loop
    // -----------------------------------------------------------------------

    public const string ReturnedFlag = "__pal_returned";
    public const string ReturnedValue = "__pal_result";
    /// <summary>R26.10. What <c>Pal.Broke()</c> names: the innermost loop's break flag.</summary>
    public const string BrokeFlag = "__pal_broke";

    private int _loopDepth;
    private int _discards;
    private IrType? _iterator;

    /// <summary>
    /// R27.42. Lowers an iterator method's body: its <c>yield</c> statements extend, and
    /// return, the sequence of values yielded so far, held in <see cref="Iterators.Trace"/>.
    /// </summary>
    public void Iterate(IrType element)
    {
        _iterator = element;
        _code.IteratorTrace = Iterators.Trace;
        _spec.IteratorTrace = Iterators.Trace;
    }

    private IrVar TraceVar(IrLoc loc) => new(loc, Iterators.Trace) { Type = new IrSeqType(_iterator!) };

    /// <summary>
    /// R27.42. The statements an iterator body is wrapped in: the trace starts empty, and
    /// falling off the end returns it.
    /// </summary>
    public IrStmt WrapIterator(IrStmt body)
    {
        var loc = body.Loc;
        var empty = new IrSpecOp(loc, "Seq.empty", []) { Type = new IrSeqType(_iterator!) };
        var inner = body is IrBlock b ? b.Statements : [body];
        return new IrBlock(loc,
            [new IrLocalDecl(loc, Iterators.Trace, new IrSeqType(_iterator!), empty), .. inner,
             new IrReturn(loc, TraceVar(loc))]);
    }

    /// <summary>
    /// R27.43. <c>out var x</c> in a loop's condition declares <c>x</c> for the loop: it is
    /// declared once, ahead of the loop, at its type's <c>default</c>. Every test writes it
    /// before anything reads it, so where it starts is never observed.
    /// </summary>
    private ImmutableArray<IrStmt> OutDeclarations(ExpressionSyntax condition, IrLoc loc)
    {
        var decls = ImmutableArray.CreateBuilder<IrStmt>();
        foreach (var arg in condition.DescendantNodesAndSelf(n => n is not AnonymousFunctionExpressionSyntax)
                     .OfType<ArgumentSyntax>())
        {
            if (!arg.RefKindKeyword.IsKind(SyntaxKind.OutKeyword) ||
                arg.Expression is not DeclarationExpressionSyntax { Designation: SingleVariableDesignationSyntax v } ||
                model.GetDeclaredSymbol(v) is not ILocalSymbol local)
                continue;
            if (known.MapType(local.Type) is not { } type || _code.DefaultValue(local.Type, loc) is not { } init)
            {
                diagnostics.Unsupported(Locations.From(arg), $"The `out var {v.Identifier.ValueText}` of type `{local.Type}`");
                continue;
            }
            decls.Add(new IrLocalDecl(loc, v.Identifier.ValueText, type, init));
        }
        return decls.ToImmutable();
    }

    /// <summary>
    /// R27.43. <c>if (e is K x)</c>, where <c>e</c> is a pointer into a region of class
    /// <c>K</c>: <c>e</c> is read once into the local <c>x</c>, and the test is that it is not
    /// null. (A pattern otherwise substitutes the subject for <c>x</c>, re-reading the heap at
    /// each use.)
    /// </summary>
    private IrStmt? RegionPatternIf(IfStatementSyntax i, IrLoc loc)
    {
        if (i.Condition is not IsPatternExpressionSyntax
            {
                Pattern: DeclarationPatternSyntax { Designation: SingleVariableDesignationSyntax v } d,
            } isp ||
            model.GetTypeInfo(isp.Expression).Type is not { } from || !known.IsRegionClass(from) ||
            model.GetTypeInfo(d.Type).Type is not { } to ||
            !SymbolEqualityComparer.Default.Equals(from.WithNullableAnnotation(NullableAnnotation.NotAnnotated),
                                                   to.WithNullableAnnotation(NullableAnnotation.NotAnnotated)) ||
            model.GetDeclaredSymbol(v) is not ILocalSymbol local ||
            known.MapType(local.Type) is not IrClassType type)
            return null;
        var name = v.Identifier.ValueText;
        var nullable = type with { Nullable = true };
        var x = new IrVar(loc, name) { Type = nullable };
        return new IrBlock(loc,
        [
            new IrLocalDecl(loc, name, nullable, _code.Lower(isp.Expression)),
            new IrIf(loc, new IrBinary(loc, BinOp.Ne, x, new IrNull(loc) { Type = nullable }) { Type = IrPrim.Bool },
                Lower(i.Statement), i.Else is null ? null : Lower(i.Else.Statement)),
        ]) { Splice = true };
    }

    private IrStmt LowerYield(YieldStatementSyntax y, IrLoc loc)
    {
        if (_iterator is not { } element) return UnsupportedStatement(y, loc);
        if (y.IsKind(SyntaxKind.YieldReturnStatement))
            return new IrAssign(loc, TraceVar(loc),
                new IrSpecOp(loc, "Seq.snoc", [TraceVar(loc), _code.ToDeclared(_code.Lower(y.Expression!), element)])
                    { Type = new IrSeqType(element) });
        if (_loopDepth == 0) return new IrReturn(loc, TraceVar(loc));
        _loopReturnVoid = true;
        return new IrBlock(loc,
        [
            new IrAssign(loc, new IrVar(loc, ReturnedFlag) { Type = IrPrim.Bool },
                new IrLiteral(loc, true) { Type = IrPrim.Bool }),
            new IrBreak(loc) { FromReturn = true },
        ]);
    }
    private ITypeSymbol? _loopReturnType;
    private IrType? _loopReturnMapped;
    private bool _loopReturnNull;
    private bool _loopReturnVoid;

    /// <summary>R30.29. The type a <c>return</c> stores: for a snapshot method, its <c>option</c>.</summary>
    private IrType? ReturnedType(ReturnStatementSyntax r) =>
        RefSnapshots.Enclosing(r, model) is { } m ? _code.SnapshotType(m) : known.MapType(ReturnType(r));

    private IrExpr Returned(ReturnStatementSyntax r, IrType? mapped) =>
        mapped is IrOptionType snapshot && RefSnapshots.Enclosing(r, model) is not null &&
        r.Expression is RefExpressionSyntax { Expression: var target }
            ? SnapshotTarget(target, snapshot)
            : _code.ToDeclared(_code.Lower(r.Expression!), mapped);

    /// <summary>
    /// R30.29. The <c>option</c> <c>ref target</c> is, in a snapshot: <c>None</c> for a null
    /// reference, another snapshot as it is, and <c>Some</c> of any other location's value.
    /// </summary>
    private IrExpr SnapshotTarget(ExpressionSyntax target, IrOptionType type) =>
        _code.LowerRaw(target, type) ??
        new IrOptionOp(Locations.From(target), OptionOpKind.Some, _code.ToDeclared(_code.Lower(target), type.Inner)) { Type = type };

    /// <summary>Whether a <c>return</c> inside a loop was rewritten, so the body needs its cells.</summary>
    public bool ReturnsInLoop => _loopReturnType is not null || _loopReturnVoid;

    /// <summary>
    /// R26.2. <c>return e;</c> inside a loop leaves its value in a cell, raises the flag,
    /// and leaves the loop: <c>{ __pal_result = e; __pal_returned = true; break; }</c>.
    /// </summary>
    private IrStmt LowerReturnInLoop(ReturnStatementSyntax r, IrLoc loc)
    {
        var stmts = ImmutableArray.CreateBuilder<IrStmt>();
        if (r.Expression is not null && ReturnType(r) is { } rt && ReturnedType(r) is { } mapped)
        {
            _loopReturnType = rt;
            _loopReturnMapped = mapped;
            _loopReturnNull = RefSnapshots.Enclosing(r, model) is not null;
            stmts.Add(new IrAssign(loc, new IrVar(loc, ReturnedValue) { Type = mapped }, Returned(r, mapped)));
        }
        else if (r.Expression is null) _loopReturnVoid = true;
        else return UnsupportedStatement(r, loc);
        stmts.Add(new IrAssign(loc, new IrVar(loc, ReturnedFlag) { Type = IrPrim.Bool },
            new IrLiteral(loc, true) { Type = IrPrim.Bool }));
        stmts.Add(new IrBreak(loc) { FromReturn = true });
        return new IrBlock(loc, stmts.ToImmutable());
    }

    /// <summary>
    /// R26.2. Lowers a loop's body one level deeper, and follows a loop a <c>return</c>
    /// left with what the <c>return</c> still owes: leaving the enclosing loop too, or
    /// returning the value.
    /// </summary>
    private IrStmt AfterLoop(Func<IrStmt> loop, IrLoc loc)
    {
        _loopDepth++;
        IrStmt lowered;
        try { lowered = loop(); }
        finally { _loopDepth--; }
        if (!ReturnsFrom(lowered)) return lowered;

        var flag = new IrVar(loc, ReturnedFlag) { Type = IrPrim.Bool };
        IrStmt owed = _loopDepth > 0
            ? new IrBreak(loc) { FromReturn = true }
            : new IrReturn(loc, _loopReturnType is not null
                ? new IrVar(loc, ReturnedValue) { Type = _loopReturnMapped }
                : _iterator is not null ? TraceVar(loc) : null);
        return new IrBlock(loc, [.. lowered is IrBlock { Splice: true } spliced ? spliced.Statements : [lowered],
            new IrIf(loc, flag, owed, null)]) { Splice = true };
    }

    private static bool ReturnsFrom(IrStmt s) => s switch
    {
        IrBreak { FromReturn: true } => true,
        IrBlock b => b.Statements.Any(ReturnsFrom),
        IrIf i => ReturnsFrom(i.Then) || (i.Else is not null && ReturnsFrom(i.Else)),
        IrWhile w => ReturnsFrom(w.Body),
        IrFor f => ReturnsFrom(f.Body),
        _ => false,
    };

    /// <summary>R26.2. The cells, declared ahead of the body: no return yet, and a default value.</summary>
    public ImmutableArray<IrStmt> ReturnCells(IrLoc loc)
    {
        if (!ReturnsInLoop) return [];
        var cells = ImmutableArray.CreateBuilder<IrStmt>();
        cells.Add(new IrLocalDecl(loc, ReturnedFlag, IrPrim.Bool, new IrLiteral(loc, false) { Type = IrPrim.Bool }));
        if (_loopReturnType is { } rt && _loopReturnMapped is { } mapped)
        {
            // R30.29. A snapshot method's cell starts as the null reference.
            if ((_loopReturnNull && mapped is IrOptionType
                    ? new IrNull(loc) { Type = mapped } : _code.DefaultValue(rt, loc)) is { } init)
                cells.Add(new IrLocalDecl(loc, ReturnedValue, mapped, init));
            else
                diagnostics.Error("PALCS0686", loc,
                    $"A `return` inside a loop of a method returning `{rt}`: the cell its value is " +
                    "kept in needs a `default`, and this type has none in the translation " +
                    "(doc/translation.md R26.2).");
        }
        return cells.ToImmutable();
    }

    // -----------------------------------------------------------------------
    // R5.14. `switch`
    // -----------------------------------------------------------------------

    /// <summary>
    /// R5.14. Lowers a <c>switch</c> to <see cref="IrSwitch"/>, which Normalize turns
    /// into an if/else chain. Two things are settled here rather than there, because
    /// both need the syntax: the scrutinee is bound to an immutable local, so that the
    /// chain tests a value C# evaluated exactly once; and the constructs the chain cannot
    /// express are refused.
    /// </summary>
    private IrStmt LowerSwitch(SwitchStatementSyntax node, IrLoc loc)
    {
        var type = known.MapType(model.GetTypeInfo(node.Expression).Type);
        if (type is null)
        {
            diagnostics.Unsupported(Locations.From(node.Expression),
                $"The type of the `switch` expression `{node.Expression}`");
            return new IrBlock(loc, []);
        }

        var scrutinee = new IrLocalDecl(loc, Fresh("switch"), type, _code.Lower(node.Expression))
            { Immutable = true };

        var sections = ImmutableArray.CreateBuilder<IrSwitchSection>();
        foreach (var section in node.Sections)
            if (LowerSwitchSection(section) is { } lowered) sections.Add(lowered);

        return new IrSwitch(loc, scrutinee, sections.ToImmutable());
    }

    private IrSwitchSection? LowerSwitchSection(SwitchSectionSyntax section)
    {
        var loc = Locations.From(section);
        var labels = ImmutableArray.CreateBuilder<IrExpr>();

        foreach (var label in section.Labels)
        {
            switch (label)
            {
                case DefaultSwitchLabelSyntax:
                    break;  // no test; an empty label list is the `default` section
                case CaseSwitchLabelSyntax { Value: { } value }:
                    labels.Add(_code.Lower(value));
                    break;
                default:
                    // A pattern label binds and tests; R5.14 compares against constants.
                    diagnostics.Unsupported(Locations.From(label),
                        $"The `switch` label `{label.ToString().Trim()}`");
                    return null;
            }
        }

        var statements = section.Statements.Select(Lower).ToImmutableArray();

        // The section's trailing `break` is the section terminator: it goes with the
        // section. Any other `break` meant "leave the switch", and after the rewrite
        // there is no switch to leave — inside a loop it would silently become the
        // loop's `break` instead.
        if (statements is [.., IrBreak]) statements = statements.RemoveAt(statements.Length - 1);
        if (LooseBreak(statements) is { } stray)
        {
            diagnostics.Error("PALCS0577", stray.Loc,
                "A `break` that leaves a `switch` early has no meaning once the `switch` " +
                "becomes an if/else chain (R5.14): there is nothing left to break out of, " +
                "and inside a loop it would become the loop's `break`. Restructure the " +
                "section so that its `break` is its last statement.");
            return null;
        }

        return new IrSwitchSection(loc, labels.ToImmutable(), statements);
    }

    /// <summary>
    /// A <c>break</c> that would be captured by the desugaring. Loops and nested
    /// <c>switch</c>es are opaque: a <c>break</c> inside one binds to it, before the
    /// rewrite and after.
    /// </summary>
    private static IrBreak? LooseBreak(IEnumerable<IrStmt> statements) =>
        statements.Select(LooseBreak).FirstOrDefault(b => b is not null);

    private static IrBreak? LooseBreak(IrStmt stmt) => stmt switch
    {
        IrBreak b => b,
        IrBlock b => LooseBreak(b.Statements),
        IrIf i => LooseBreak(i.Then) ?? (i.Else is null ? null : LooseBreak(i.Else)),
        _ => null,
    };

    private int _temps;
    private string Fresh(string hint) => $"__pal_{hint}{_temps++}";

    private IrStmt LowerLocalDeclaration(LocalDeclarationStatementSyntax node, IrLoc loc)
    {
        var declared = node.Declaration;
        var statements = ImmutableArray.CreateBuilder<IrStmt>();

        foreach (var v in declared.Variables)
        {
            var symbol = model.GetDeclaredSymbol(v) as ILocalSymbol;
            var type = known.MapType(symbol?.Type);
            if (type is null)
            {
                diagnostics.Unsupported(Locations.From(v), $"The local type `{declared.Type}`");
                continue;
            }
            // R24.8. A `ref` local bound to an array element is that element: its index is
            // evaluated once, into a fresh local, and every use of the name is the element
            // at that local.
            if (symbol is { RefKind: RefKind.Ref or RefKind.RefReadOnly })
            {
                if (SnapshotLocal(v, symbol, node, statements)) continue;
                if (ReboundRefLocal(v, symbol, node, statements)) continue;
                if (RefLocal(v, symbol, node, statements) is null && !_staleReported.Contains(symbol))
                    diagnostics.Unsupported(Locations.From(v), $"The `ref` local `{v.Identifier.ValueText}`",
                        "Only `ref` locals bound to an element of an array named by an unrebound " +
                        "local or an unwritten field, and never rebound, are supported (doc/translation.md R24.8), " +
                        "or bound, by statements, to elements of one field's array and used only while bound " +
                        "since the field last changed (R30.1).");
                continue;
            }
            // R28.2. `C list = _list;`, never written, in a borrowing struct's member is
            // another name for the borrowed object.
            if (borrow is not null && symbol is not null && v.Initializer?.Value is { } bi &&
                model.GetSymbolInfo(bi).Symbol is IFieldSymbol bf && borrow.IsOwner(bf) &&
                NeverWritten(symbol, node.Parent ?? node))
            {
                _code.Alias(symbol, _code.Lower(bi));
                _spec.Alias(symbol, _spec.Lower(bi));
                continue;
            }
            // R28.2. So is `T[] a = list._items;`, never written, for the borrowed object's
            // array: the object is only read, so the field holds that array throughout.
            if (borrow is not null && symbol is { Type: IArrayTypeSymbol } && v.Initializer?.Value is { } ai &&
                NeverWritten(symbol, node.Parent ?? node) &&
                _code.Lower(ai) is IrField { Receiver: IrVar { Name: Pal.Compiler.Emit.Names.This } } arrayField)
            {
                _code.Alias(symbol, arrayField);
                _spec.Alias(symbol, arrayField);
                continue;
            }
            // R32.14. `V? x = this as V;` in a member of a view's base: `x` is null.
            if (symbol is not null && v.Initializer?.Value is { } viewInit &&
                NeverWritten(symbol, node.Parent ?? node) && _code.AbsentView(symbol, viewInit))
                continue;
            // R27.46. `C? x = p as C;`, never written, where `p` is an `[Exactly(typeof(C))]`
            // parameter: `p` is a `C`, so `x` is another name for it.
            if (symbol is not null && v.Initializer?.Value is { } asInit &&
                ExprLowerer.Unparenthesized(asInit) is BinaryExpressionSyntax { RawKind: (int)SyntaxKind.AsExpression } asExpr &&
                model.GetSymbolInfo(asExpr.Left).Symbol is IParameterSymbol ap &&
                FrontendPass.ExactParameter(ap, model.Compilation, known) is { } apClass &&
                model.GetTypeInfo(asExpr.Right).Type is { } asTarget &&
                SymbolEqualityComparer.Default.Equals(asTarget.WithNullableAnnotation(NullableAnnotation.NotAnnotated),
                    apClass.WithNullableAnnotation(NullableAnnotation.NotAnnotated)) &&
                NeverWritten(symbol, node.Parent ?? node))
            {
                var pType = known.MapType(apClass);
                _code.Alias(symbol, new IrVar(Locations.From(v), ap.Name) { Type = pType });
                _spec.Alias(symbol, new IrVar(Locations.From(v), ap.Name) { Type = pType });
                continue;
            }
            // R27.50. `D? x = e as D;`, never written, where R27.46 decided the `as` false
            // (`this as Sub` on an object of its exact class): `x` is another name for `null`.
            if (symbol is not null && v.Initializer?.Value is { } nullInit &&
                ExprLowerer.Unparenthesized(nullInit) is BinaryExpressionSyntax { RawKind: (int)SyntaxKind.AsExpression } &&
                NeverWritten(symbol, node.Parent ?? node) &&
                _code.Lower(nullInit) is IrNull { Type: IrClassType { Nullable: true } } folded)
            {
                _code.Alias(symbol, folded);
                _spec.Alias(symbol, folded);
                continue;
            }
            // R27.41. A borrowing struct of the method's own object, held in a local.
            if (borrow is null && symbol is not null && HeldStruct(v, symbol, type, statements)) continue;
            // R24.19. `T[] a = _field;`, never written, is another name for the field.
            if (symbol is not null && FieldAlias(v, symbol, node) is { } aliased)
            {
                _code.Alias(symbol, aliased.Code);
                _spec.Alias(symbol, aliased.Spec);
                continue;
            }
            // R30.7. `T x = f = e;`, `f` a field of `this` or a local: the assignment, then
            // `x` initialised with what it stored, read back (not null where C# says so).
            if (symbol is not null && v.Initializer?.Value is { } chainInit &&
                ExprLowerer.Unparenthesized(chainInit) is AssignmentExpressionSyntax { RawKind: (int)SyntaxKind.SimpleAssignmentExpression } chain &&
                chain.Right is not RefExpressionSyntax && !known.IsGhost(symbol.Type) &&
                model.GetSymbolInfo(chain.Left).Symbol is ILocalSymbol or IFieldSymbol { IsStatic: false } &&
                chain.Left is IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax })
            {
                statements.Add(LowerAssignment(chain, Locations.From(chain)));
                var stored = _code.Lower(chain.Left);
                if (stored.Type is IrOptionType storedOption && type is not IrOptionType && ExprLowerer.SameType(storedOption.Inner, type))
                    stored = new IrOptionOp(stored.Loc, OptionOpKind.Value, stored) { Type = type };
                statements.Add(new IrLocalDecl(Locations.From(v), v.Identifier.ValueText, type, _code.ToDeclared(stored, type))
                {
                    Immutable = type is IrPrim { Kind: PrimKind.Bool or PrimKind.String } or IrOptionType
                                    or IrUserSpecType or IrExnType &&
                                NeverWritten(symbol, node.Parent ?? node),
                });
                continue;
            }
            // R24.12. A `Ghost<T>` local is a snapshot: a ghost name for a specification
            // value (`Pal.Contents(a)`, a model), fixed at its declaration, that later ghost
            // statements can mention.
            if (known.IsGhost(symbol?.Type))
            {
                if (v.Initializer is null || !NeverWritten(symbol!, node.Parent ?? node))
                {
                    diagnostics.Unsupported(Locations.From(v),
                        "A `Ghost<T>` local without an initialiser, or one that is assigned",
                        "A ghost local names one specification value for its whole life.");
                    continue;
                }
                statements.Add(new IrGhostStmt(Locations.From(v), GhostKind.Let,
                    _code.Lower(v.Initializer.Value), v.Identifier.ValueText) { Type = type });
                continue;
            }
            statements.Add(new IrLocalDecl(Locations.From(v), v.Identifier.ValueText, type,
                v.Initializer is null ? null : _code.ToDeclared(_code.Lower(v.Initializer.Value), type))
            {
                Immutable = v.Initializer is not null && symbol is not null &&
                            type is IrPrim { Kind: PrimKind.Bool or PrimKind.String } or IrOptionType
                                or IrUserSpecType or IrExnType &&
                            NeverWritten(symbol, node.Parent ?? node),
            });
        }

        // `T a, b;` declares both names in the enclosing block: the enclosing block splices them.
        return statements.Count == 1 ? statements[0] : new IrBlock(loc, statements.ToImmutable()) { Splice = true };
    }

    /// <summary>
    /// R27.41. <c>S e = new S(this, a…);</c> in an instance method of the class a borrowing
    /// struct <c>S</c> borrows: the local holds the struct, and each object the struct owns
    /// is held in a further local of its own, as the struct's members expect it. Both
    /// lowerers record the local, so that its members can be called and its <c>[Spec]</c>
    /// properties read. <c>false</c> when the declaration is not one.
    /// </summary>
    private bool HeldStruct(VariableDeclaratorSyntax v, ILocalSymbol symbol, IrType type,
        ImmutableArray<IrStmt>.Builder statements)
    {
        // R32.13. A local of a view's base class, initialised by a call returning the view
        // exactly (or by the view's constructor), holds the view's record.
        var viewInit = v.Initializer?.Value is { } vi ? Unparenthesized(vi) switch
        {
            BaseObjectCreationExpressionSyntax c when model.GetTypeInfo(c).Type is INamedTypeSymbol ct &&
                Borrowing.IsView(ct, known) => ct,
            InvocationExpressionSyntax c when model.GetSymbolInfo(c).Symbol is IMethodSymbol cm &&
                FrontendPass.ExactReturn(cm, known) is { } ex => ex,
            _ => null,
        } : null;
        INamedTypeSymbol st;
        if (symbol.Type is INamedTypeSymbol { TypeKind: TypeKind.Struct } bst && Borrowing.IsBorrowing(bst, known)) st = bst;
        else if (viewInit is not null && known.MapType(viewInit) is { } viewType) { st = viewInit; type = viewType; }
        else return false;
        var loc = Locations.From(v);
        var owner = Borrowing.OwnerField(st, known)!;
        var self = symbol.ContainingSymbol as IMethodSymbol;
        var creation = v.Initializer?.Value as BaseObjectCreationExpressionSyntax;
        var args = creation?.ArgumentList?.Arguments ?? default;
        var op = creation is not null && model.GetSymbolInfo(creation).Symbol is IMethodSymbol ctor
            ? Borrowing.OwnerParameter(ctor, owner, known.Compilation) : null;
        ExpressionSyntax? ownerArg = op is null || creation?.ArgumentList is null ? null
            : args.FirstOrDefault(a => a.NameColon?.Name.Identifier.ValueText == op.Name)?.Expression ??
              (op.Ordinal < args.Count && args[op.Ordinal].NameColon is null ? args[op.Ordinal].Expression : null);
        // R27.49. `x.GetEnumerator()`: a method of the owner class that returns the struct,
        // called on `this` or on another object of the class.
        ExpressionSyntax? init = creation;
        if (creation is null && v.Initializer?.Value is InvocationExpressionSyntax inv &&
            model.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: false } getter &&
            SymbolEqualityComparer.Default.Equals(
                (FrontendPass.ExactReturn(getter, known) ?? getter.ReturnType).OriginalDefinition, st.OriginalDefinition) &&
            SymbolEqualityComparer.Default.Equals(getter.ContainingType.OriginalDefinition, owner.Type.OriginalDefinition))
        {
            init = inv;
            ownerArg = inv.Expression is MemberAccessExpressionSyntax ma ? ma.Expression : SyntaxFactory.ThisExpression();
        }
        // R27.49. The owner: `this`, or a parameter of the owner class (or a local naming one).
        string? ownerName = ownerArg is ThisExpressionSyntax ? Pal.Compiler.Emit.Names.This
            : ownerArg is IdentifierNameSyntax && _code.Lower(ownerArg) is IrVar { Name: var ov } &&
              self?.Parameters.FirstOrDefault(q => q.Name == ov) is { } oq &&
              (SymbolEqualityComparer.Default.Equals(oq.Type.OriginalDefinition, owner.Type.OriginalDefinition) ||
               SymbolEqualityComparer.Default.Equals(
                   FrontendPass.ExactParameter(oq, known.Compilation, known)?.OriginalDefinition, owner.Type.OriginalDefinition))
                ? ov : null;
        if (init is null || ownerName is null ||
            self is null || self.IsStatic || self.MethodKind == MethodKind.LambdaMethod ||
            !SymbolEqualityComparer.Default.Equals(self.ContainingType?.OriginalDefinition, owner.Type.OriginalDefinition) ||
            known.MapType(owner.Type) is not IrClassType ownerType ||
            v.Parent?.Parent is not LocalDeclarationStatementSyntax { Parent: BlockSyntax } decl ||
            decl.Ancestors().TakeWhile(a => a is not (BaseMethodDeclarationSyntax or AccessorDeclarationSyntax))
                .Any(a => a is WhileStatementSyntax or DoStatementSyntax or ForStatementSyntax or
                          CommonForEachStatementSyntax or AnonymousFunctionExpressionSyntax or
                          LocalFunctionStatementSyntax or TryStatementSyntax or SwitchSectionSyntax))
        {
            diagnostics.Error("PALCS0710", loc,
                $"The local `{v.Identifier.ValueText}` holds a struct that borrows its collection. Such a " +
                "local is declared in a block of an instance method of the borrowed class, outside any loop, " +
                "lambda or `try`, " +
                "and initialised by the struct's constructor, or a method of the class returning it, applied " +
                "to `this` or to a parameter of the class (doc/translation.md R27.41, R27.49).");
            return true;
        }
        var name = v.Identifier.ValueText;
        var owned = Borrowing.OwnedFields(st, known);
        var held = new BorrowContext(st, owner, type, ownerType, false, null)
        {
            ViewBase = Borrowing.ViewBase(st, known),
            Owned = owned,
            SelfName = name,
            OwnerName = ownerName,
            OwnedNames = owned.ToImmutableDictionary(f => f.Name, f => $"__pal_own_{name}{f.Name}"),
        };
        var ownedLocals = ImmutableArray.CreateBuilder<(string, string, IrClassType)>();
        foreach (var f in owned)
            if (known.MapType(f.Type) is IrClassType ot) ownedLocals.Add((f.Name, held.OwnedLocal(f), ot));
        statements.Add(new IrLocalDecl(loc, name, type, _code.Lower(init))
        {
            Owned = ownedLocals.ToImmutable(),
            HeldOwner = ownerName == Pal.Compiler.Emit.Names.This ? null : ownerName,
        });
        _code.Hold(symbol, held);
        _spec.Hold(symbol, held);
        return true;
    }

    /// <summary>
    /// R24.19. An array local initialised from an instance field of the class, written
    /// nowhere in its scope, in a scope that neither assigns that field nor calls another
    /// instance method of the class (either could replace the field's array): every use
    /// of the local is a use of the field. A cell holding the reference would hide from
    /// the verifier that the array it points to is the one the class invariant describes.
    /// </summary>
    private (IrExpr Code, IrExpr Spec)? FieldAlias(VariableDeclaratorSyntax v, ILocalSymbol symbol, SyntaxNode node)
    {
        if (symbol.Type is not IArrayTypeSymbol || v.Initializer?.Value is not { } init) return null;
        while (init is ParenthesizedExpressionSyntax p) init = p.Expression;
        if (init is not (IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }))
            return null;
        if (model.GetSymbolInfo(init).Symbol is not IFieldSymbol { IsStatic: false } field ||
            !SymbolEqualityComparer.Default.Equals(field.ContainingType.OriginalDefinition,
                symbol.ContainingSymbol.ContainingType?.OriginalDefinition))
            return null;
        var scope = node.Parent ?? node;
        // Writing an element writes the field's array; only rebinding the name matters.
        bool Names(ExpressionSyntax? e)
        {
            while (e is ParenthesizedExpressionSyntax p) e = p.Expression;
            return e is IdentifierNameSyntax &&
                   SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(e).Symbol, symbol);
        }
        // R30.2 / R33.17. `a = _f;` as a statement rebinds the local to the field.
        bool Rebind(AssignmentExpressionSyntax a) =>
            a.IsKind(SyntaxKind.SimpleAssignmentExpression) && a.Parent is ExpressionStatementSyntax &&
            Names(a.Left) && (a.Right is IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }) &&
            SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Right).Symbol?.OriginalDefinition, field.OriginalDefinition);
        var rebinds = scope.DescendantNodes().OfType<AssignmentExpressionSyntax>().Where(Rebind).ToList();
        if (scope.DescendantNodes().Any(n => n switch
            {
                AssignmentExpressionSyntax a => Names(a.Left) && !rebinds.Contains(a),
                ArgumentSyntax { RefKindKeyword.RawKind: not (int)SyntaxKind.None } arg => Names(arg.Expression),
                _ => false,
            }))
            return null;
        // R33.17. Whatever may replace the field after the declaration is a statement that the
        // next statement of its block follows by re-reading it; a call that cannot replace it
        // is harmless.
        bool resynced = true;
        foreach (var n in scope.DescendantNodes().Where(n => n.SpanStart > v.SpanStart))
        {
            if (!Replaces(n, field)) continue;
            var stmt = n.Parent as ExpressionStatementSyntax;
            var block = stmt?.Parent as BlockSyntax;
            var at = block?.Statements.IndexOf(stmt!) ?? -1;
            if (stmt?.Expression != n || block is null || at + 1 >= block.Statements.Count ||
                block.Statements[at + 1] is not ExpressionStatementSyntax { Expression: AssignmentExpressionSyntax next } ||
                !rebinds.Contains(next))
            {
                resynced = false;
                break;
            }
        }
        if (resynced)
        {
            foreach (var r in rebinds) _resyncs.Add(r.Parent!);
            _fieldAliases[symbol] = field;
            return (_code.Lower(init), _spec.Lower(init));
        }
        // R30.33. Otherwise, a local that keeps the array the field's one replacement discards.
        if (rebinds.Count == 0 && KeptAt(v, symbol, field, scope, Names) is { } keeper)
        {
            _keepers[keeper] = symbol;
            return (_code.Lower(init), _spec.Lower(init));
        }
        // R30.2. Otherwise the flow check: the local is rebound wherever the field may have changed.
        if (rebinds.Count == 0) return null;
        var flow = new AliasFlow(model, known, symbol, new HashSet<ISymbol>(SymbolEqualityComparer.Default) { field },
            e => e.Expression is AssignmentExpressionSyntax a && rebinds.Contains(a));
        if (!flow.Check(scope, node, current: true)) { StaleAlias(symbol, flow); return null; }
        _fieldRebinds.Add(symbol);
        return (_code.Lower(init), _spec.Lower(init));
    }

    /// <summary>
    /// R30.33. <c>T[]? a = _f;</c>, never written, where the first thing after it that may
    /// replace <c>_f</c> is a statement <c>_f = e;</c> of the declaration's own block (with
    /// <c>e</c> not <c>a</c>), and <c>a</c> is not null wherever it is used after that
    /// statement: up to the statement <c>a</c> is the field (R24.19); the statement hands
    /// the old array to <c>a</c>, which owns it from then on, as a fresh array local does
    /// (R6.11a). The statement, or <c>null</c>.
    /// </summary>
    private ExpressionStatementSyntax? KeptAt(VariableDeclaratorSyntax v, ILocalSymbol symbol, IFieldSymbol field,
        SyntaxNode scope, Func<ExpressionSyntax?, bool> names)
    {
        if (v.Parent?.Parent is not LocalDeclarationStatementSyntax { Parent: BlockSyntax block }) return null;
        var first = scope.DescendantNodes().Where(n => n.SpanStart > v.SpanStart && Replaces(n, field))
            .OrderBy(n => n.SpanStart).FirstOrDefault();
        if (first is not AssignmentExpressionSyntax { RawKind: (int)SyntaxKind.SimpleAssignmentExpression } a ||
            a.Parent is not ExpressionStatementSyntax stmt || stmt.Parent != block || names(a.Right) ||
            a.Left is not (IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }))
            return null;
        var uses = scope.DescendantNodes().OfType<IdentifierNameSyntax>()
            .Where(id => id.SpanStart > stmt.Span.End &&
                         SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(id).Symbol, symbol))
            .ToList();
        if (uses.Count == 0 || uses.Any(id => model.GetTypeInfo(id).Nullability.FlowState != NullableFlowState.NotNull))
            return null;
        return stmt;
    }

    /// <summary>R30.33. The statement that hands a replaced field's array to each keeping local.</summary>
    private readonly Dictionary<SyntaxNode, ILocalSymbol> _keepers = [];

    /// <summary>
    /// R30.33. <c>_f = e;</c> for a local that keeps <c>_f</c>'s array: the local, declared
    /// from the field, then the assignment, after which the name is the local.
    /// </summary>
    private IrStmt KeepAndReplace(ExpressionStatementSyntax node, ILocalSymbol kept, IrLoc loc)
    {
        var a = (AssignmentExpressionSyntax)node.Expression;
        var type = known.MapType(kept.Type)!;
        var decl = new IrLocalDecl(loc, kept.Name, type, _code.Lower(a.Left)) { TakesField = true };
        var store = LowerSideEffect(node.Expression, loc);
        _code.Alias(kept, new IrVar(loc, kept.Name) { Type = type });
        _spec.Alias(kept, new IrVar(loc, kept.Name) { Type = type });
        return new IrBlock(loc, [decl, store]) { Splice = true };
    }

    /// <summary>R30.29. The <c>option</c> type of each snapshot <c>ref</c> local.</summary>
    private readonly Dictionary<ISymbol, IrOptionType> _snapshotLocals = new(SymbolEqualityComparer.Default);

    private void RegisterSnapshot(ILocalSymbol symbol, IrOptionType type, IrLoc loc)
    {
        _snapshotLocals[symbol] = type;
        var raw = new IrVar(loc, symbol.Name) { Type = type };
        _code.Snapshot(symbol, raw);
        _spec.Snapshot(symbol, raw);
    }

    /// <summary>The block a declaration is in, past the labels on it.</summary>
    private static SyntaxNode BlockOf(SyntaxNode node) =>
        node.Ancestors().FirstOrDefault(a => a is not LabeledStatementSyntax) ?? node;

    /// <summary>
    /// R30.29. A <c>ref</c> local in a snapshot method, or bound to a call of one, is an
    /// <c>option</c> local: <c>None</c> where it is a null reference, <c>Some</c> of the value
    /// it refers to otherwise, read when it is bound (<see cref="RefSnapshots"/>). It may be
    /// rebound, by a statement, only in a snapshot method; it is never written through, nor
    /// passed by reference except to <c>Unsafe.IsNullRef</c>; and outside a snapshot method,
    /// nothing may write the object's state while it is live.
    /// </summary>
    private bool SnapshotLocal(VariableDeclaratorSyntax v, ILocalSymbol symbol, SyntaxNode node,
        ImmutableArray<IrStmt>.Builder statements)
    {
        if (v.Initializer?.Value is not RefExpressionSyntax { Expression: var target }) return false;
        var inner = target;
        while (inner is ParenthesizedExpressionSyntax or PostfixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.SuppressNullableWarningExpression })
            inner = inner is ParenthesizedExpressionSyntax p ? p.Expression : ((PostfixUnaryExpressionSyntax)inner).Operand;
        var method = RefSnapshots.Enclosing(node, model);
        var call = inner is InvocationExpressionSyntax inv && model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee &&
                   RefSnapshots.IsSnapshot(callee, model.Compilation);
        if (method is null && !call) return false;
        if (known.MapType(symbol.Type) is not { } element) return false;
        var type = new IrOptionType(element);
        var loc = Locations.From(v);
        var scope = BlockOf(node);
        if (SnapshotRefusal(symbol, scope, node, method) is { } why)
        {
            diagnostics.Error("PALCS0751", loc,
                $"`{symbol.Name}` holds a reference that may be null, read once as an `option` " +
                $"(doc/translation.md R30.29), but {why}.");
            return true;
        }
        var rebound = scope.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a =>
            SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, symbol));
        statements.Add(new IrLocalDecl(loc, symbol.Name, type, SnapshotTarget(target, type)) { Immutable = !rebound });
        RegisterSnapshot(symbol, type, loc);
        return true;
    }

    /// <summary>R30.29. Why the snapshot local <paramref name="symbol"/> cannot be one, if it cannot.</summary>
    private string? SnapshotRefusal(ILocalSymbol symbol, SyntaxNode scope, SyntaxNode decl, IMethodSymbol? method)
    {
        ExpressionSyntax Root(ExpressionSyntax e)
        {
            while (true)
            {
                switch (e)
                {
                    case ParenthesizedExpressionSyntax p: e = p.Expression; continue;
                    case PostfixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.SuppressNullableWarningExpression } sn: e = sn.Operand; continue;
                    case MemberAccessExpressionSyntax { RawKind: (int)SyntaxKind.SimpleMemberAccessExpression } m: e = m.Expression; continue;
                    case ElementAccessExpressionSyntax el: e = el.Expression; continue;
                    default: return e;
                }
            }
        }
        bool Is(ExpressionSyntax e) => Root(e) is IdentifierNameSyntax &&
            SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(Root(e)).Symbol, symbol);
        bool SnapshotSink(SyntaxNode? n) => n switch
        {
            ReturnStatementSyntax => true,
            EqualsValueClauseSyntax { Parent: VariableDeclaratorSyntax d } =>
                model.GetDeclaredSymbol(d) is ILocalSymbol { IsRef: true },
            AssignmentExpressionSyntax a => model.GetSymbolInfo(a.Left).Symbol is ILocalSymbol { IsRef: true },
            _ => false,
        };
        foreach (var n in scope.DescendantNodes())
        {
            var written = n switch
            {
                AssignmentExpressionSyntax a => a.Left,
                PrefixUnaryExpressionSyntax u when u.IsKind(SyntaxKind.PreIncrementExpression) ||
                                                   u.IsKind(SyntaxKind.PreDecrementExpression) => u.Operand,
                PostfixUnaryExpressionSyntax u when u.IsKind(SyntaxKind.PostIncrementExpression) ||
                                                    u.IsKind(SyntaxKind.PostDecrementExpression) => u.Operand,
                _ => null,
            };
            if (written is not null && Is(written))
            {
                if (n is AssignmentExpressionSyntax { RawKind: (int)SyntaxKind.SimpleAssignmentExpression, Right: RefExpressionSyntax, Left: IdentifierNameSyntax } rebind &&
                    rebind.Parent is ExpressionStatementSyntax)
                {
                    if (method is null) return "it is rebound outside the method that may return a null reference";
                    continue;
                }
                return "it is written through";
            }
            if (n is ArgumentSyntax { RefKindKeyword.RawKind: not (int)SyntaxKind.None } arg && Is(arg.Expression) &&
                !(arg.Parent?.Parent is InvocationExpressionSyntax isNull &&
                  model.GetSymbolInfo(isNull).Symbol is IMethodSymbol isNullMethod && RefSnapshots.IsIsNullRef(isNullMethod)))
                return "it is passed by reference to something other than `Unsafe.IsNullRef`";
            if (n is RefExpressionSyntax r && Is(r.Expression) && (method is null || !SnapshotSink(r.Parent)))
                return "a reference into it is taken other than to return it or bind another such local";
        }
        if (method is not null)
            return Declarations.IsReadOnly(method, model.Compilation, known) ? null
                : $"`{method.Name}` may write its object's state, which the reference would see";
        var live = LiveStretch(scope, decl, symbol);
        if (Declarations.MutatesAt(scope, live, model, known) || WritesArrayAt(scope, live))
            return "the object's state, or an array, may be written while it is live";
        return null;
    }

    /// <summary>
    /// R30.29. Whether an array element may be written in <paramref name="at"/>: through any
    /// array, a parameter's too, which <see cref="Declarations.MutatesAt"/> does not count
    /// as the object's state; or by a call that is passed an array and whose body writes an
    /// element or passes an array on.
    /// </summary>
    private bool WritesArrayAt(SyntaxNode scope, Func<SyntaxNode, bool> at)
    {
        static bool WritesElement(SyntaxNode n) => n switch
        {
            AssignmentExpressionSyntax a => a.Left is ElementAccessExpressionSyntax,
            PrefixUnaryExpressionSyntax u => u.Operand is ElementAccessExpressionSyntax,
            PostfixUnaryExpressionSyntax u => u.Operand is ElementAccessExpressionSyntax,
            ArgumentSyntax { RefKindKeyword.RawKind: not (int)SyntaxKind.None } arg => arg.Expression is ElementAccessExpressionSyntax,
            _ => false,
        };
        static bool PassesArray(InvocationExpressionSyntax call, SemanticModel m) =>
            call.ArgumentList.Arguments.Any(a => m.GetTypeInfo(a.Expression).Type is IArrayTypeSymbol);
        var visiting = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        bool Writes(InvocationExpressionSyntax call, SemanticModel m)
        {
            if (!PassesArray(call, m)) return false;
            if (m.GetSymbolInfo(call).Symbol is not IMethodSymbol callee) return true;
            if (RefSnapshots.IsIsNullRef(callee) || callee.ContainingNamespace?.ToDisplayString() == "PalLang") return false;
            if (callee.GetAttributes().Any(a => a.AttributeClass?.Name is "SpecAttribute" or "LemmaAttribute" or "PureAttribute"))
                return false;
            var body = callee.OriginalDefinition.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).FirstOrDefault();
            if (body is null || !m.Compilation.ContainsSyntaxTree(body.SyntaxTree)) return true;
            if (!visiting.Add(callee.OriginalDefinition)) return false;
            var calleeModel = m.Compilation.GetSemanticModel(body.SyntaxTree);
            return body.DescendantNodes().Any(n => WritesElement(n) ||
                n is InvocationExpressionSyntax inner && Writes(inner, calleeModel));
        }
        return scope.DescendantNodes().Where(at).Any(n =>
            WritesElement(n) || n is InvocationExpressionSyntax call && Writes(call, model));
    }

    /// <summary>R33.5. The index local of each rebound <c>ref</c> local.</summary>
    private readonly Dictionary<ISymbol, IrVar> _rebound = new(SymbolEqualityComparer.Default);

    /// <summary>
    /// R33.5. A <c>ref</c> local that is rebound, <c>x = ref a[e];</c>, where every binding
    /// (its initialiser too, unless that is <c>ref Unsafe.NullRef&lt;T&gt;()</c>) is an element
    /// of the same array <c>a</c>, named by a local that is never assigned or by a field of
    /// this object that the scope neither assigns nor can replace by a call. The local is
    /// then a mutable index into <c>a</c>: each binding assigns the index, and each use of
    /// the name is <c>a[index]</c>. A null reference is the index <c>-1</c>, so that a use
    /// of it is an out-of-bounds access the proof must rule out.
    /// </summary>
    private bool ReboundRefLocal(VariableDeclaratorSyntax v, ILocalSymbol symbol, SyntaxNode node,
        ImmutableArray<IrStmt>.Builder statements)
    {
        if (v.Initializer?.Value is not RefExpressionSyntax { Expression: var init }) return false;
        var scope = node.Parent ?? node;
        static ExpressionSyntax Strip(ExpressionSyntax e)
        {
            while (e is ParenthesizedExpressionSyntax p) e = p.Expression;
            return e;
        }
        var writes = scope.DescendantNodes().OfType<AssignmentExpressionSyntax>()
            .Where(a => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(Strip(a.Left)).Symbol, symbol) &&
                        Strip(a.Left) is IdentifierNameSyntax)
            .ToList();
        if (writes.Count == 0 || writes.Any(a => a.Right is not RefExpressionSyntax || a.Parent is not ExpressionStatementSyntax))
            return false;
        var nullRef = Strip(init) is InvocationExpressionSyntax { ArgumentList.Arguments.Count: 0 } call &&
                      model.GetSymbolInfo(call).Symbol is IMethodSymbol
                      {
                          Name: "NullRef", ContainingType: { Name: "Unsafe", ContainingNamespace: var ns }
                      } && ns.ToDisplayString() == "System.Runtime.CompilerServices";
        var targets = writes.Select(a => Strip(((RefExpressionSyntax)a.Right).Expression)).ToList();
        if (!nullRef) targets.Insert(0, Strip(init));
        if (targets.Any(t => t is not ElementAccessExpressionSyntax
            {
                ArgumentList.Arguments.Count: 1,
                Expression: IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax },
            }))
            return false;
        var arrays = targets.Cast<ElementAccessExpressionSyntax>().Select(t => t.Expression).ToList();
        var root = model.GetSymbolInfo(arrays[0]).Symbol;
        if (root is not (ILocalSymbol { Type: IArrayTypeSymbol } or IFieldSymbol { IsStatic: false, Type: IArrayTypeSymbol }) ||
            arrays.Any(a => !SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a).Symbol, root)))
            return false;
        // The array a binding names must be the array every use reads.
        var self = symbol.ContainingSymbol.ContainingType;
        foreach (var n in scope.DescendantNodes())
        {
            if (n is AssignmentExpressionSyntax a &&
                SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(Strip(a.Left)).Symbol, root))
                return false;
            if (n is ArgumentSyntax { RefKindKeyword.RawKind: not (int)SyntaxKind.None } arg &&
                SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(Strip(arg.Expression)).Symbol, root))
                return false;
            if (root is IFieldSymbol && n is InvocationExpressionSyntax inv &&
                model.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: false, ReturnsByRef: false } m &&
                SymbolEqualityComparer.Default.Equals(m.ContainingType?.OriginalDefinition, self?.OriginalDefinition) &&
                !Declarations.Has(m, known.LemmaAttribute))
                return false;
        }
        var loc = Locations.From(v);
        IrExpr initIndex;
        if (nullRef) initIndex = new IrLiteral(loc, -1) { Type = IrPrim.Int };
        else if (_code.Lower(Strip(init)) is IrElement e) initIndex = e.Index;
        else return false;
        var index = new IrVar(loc, Fresh("ref")) { Type = IrPrim.Int };
        statements.Add(new IrLocalDecl(loc, index.Name, IrPrim.Int, _code.ToDeclared(initIndex, IrPrim.Int)));
        var arraySyntax = arrays[0];
        _rebound[symbol] = index;
        _code.LazyAlias(symbol, () => new IrElement(loc, _code.Lower(arraySyntax), index)
            { Type = known.MapType(symbol.Type) });
        _spec.LazyAlias(symbol, () => new IrElement(loc, _spec.Lower(arraySyntax), index)
            { Type = known.MapType(symbol.Type) });
        return true;
    }

    private IrExpr? RefLocal(VariableDeclaratorSyntax v, ILocalSymbol symbol, SyntaxNode node,
        ImmutableArray<IrStmt>.Builder statements)
    {
        if (v.Initializer?.Value is not RefExpressionSyntax { Expression: var target }) return null;
        var scope = node.Parent ?? node;
        var rebinds = scope.DescendantNodes().OfType<AssignmentExpressionSyntax>().Where(a =>
                a.Right is RefExpressionSyntax &&
                SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, symbol)).ToList();
        if (rebinds.Count > 0 || IsNullRef(target))
            return RebindableRefLocal(v, symbol, node, target, rebinds, statements);
        // `x = ref e` rebinds; any other write goes through the alias, to the element.
        if (scope.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a =>
                a.Right is RefExpressionSyntax &&
                SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, symbol)))
            return null;
        while (target is ParenthesizedExpressionSyntax p) target = p.Expression;
        var root = target is ElementAccessExpressionSyntax { Expression: var arr }
            ? model.GetSymbolInfo(arr).Symbol : null;
        // Writing an element is seen through the alias; rebinding the array's name is not.
        // R30.16. Only while the alias is live: from its declaration to its last use, when
        // the block has no jumps. A local that is R24.19's or R30.2's name for a field is
        // the field there, so the field must not change in that stretch either.
        // R33.17. Otherwise, only a rebinding the alias can see, after its declaration; one
        // that re-reads a field alias (R24.19) leaves the local naming the same field.
        var viaLive = false;
        if (root is ILocalSymbol al)
        {
            var live = LiveStretch(scope, node, symbol);
            viaLive = !scope.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a => live(a) &&
                    SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, al)) &&
                !(al.DeclaringSyntaxReferences is [var ad] && ad.GetSyntax() is VariableDeclaratorSyntax { Initializer.Value: var av } &&
                  model.GetSymbolInfo(av).Symbol is IFieldSymbol { IsStatic: false } liveField &&
                  ChangesFields(scope, symbol, new HashSet<ISymbol>(SymbolEqualityComparer.Default) { liveField }, live));
            if (!viaLive && scope.DescendantNodes().OfType<AssignmentExpressionSyntax>()
                    .Any(a => a.SpanStart > v.SpanStart && !_resyncs.Contains(a.Parent!) &&
                              SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, al)))
                return null;
        }
        if (root is IParameterSymbol) return null;
        // A field may be replaced by an assignment or by a call of another method of the
        // class; the alias would then name the new array's element, not the old one. The
        // fields the alias can depend on are the array's own, or every field the inlined
        // `ref`-returning method mentions; assigning any other field is harmless.
        var aliasOf = !viaLive && root is ILocalSymbol rl && _fieldAliases.TryGetValue(rl, out var af0) ? af0 : null;
        if (target is InvocationExpressionSyntax || root is IFieldSymbol || aliasOf is not null)
        {
            var read = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            if (root is IFieldSymbol rf) read.Add(rf);
            if (aliasOf is not null) read.Add(aliasOf);
            if (target is InvocationExpressionSyntax call &&
                model.GetSymbolInfo(call).Symbol is IMethodSymbol { DeclaringSyntaxReferences: [var callee] } &&
                callee.SyntaxTree == model.SyntaxTree)
                foreach (var id in callee.GetSyntax().DescendantNodes().OfType<IdentifierNameSyntax>())
                    if (model.GetSymbolInfo(id).Symbol is IFieldSymbol f) read.Add(f);
            // R33.17. Only what follows the declaration, and only what may replace a field
            // the alias depends on.
            foreach (var n in scope.DescendantNodes().Where(n => n.SpanStart > v.SpanStart))
                if (read.OfType<IFieldSymbol>().Any(f => Replaces(n, f)))
                    return null;
        }
        if (_code.Lower(v.Initializer.Value) is not IrElement element) return null;
        var index = Fresh("ref");
        var indexType = element.Index.Type ?? IrPrim.Int;
        statements.Add(new IrLocalDecl(Locations.From(v), index, indexType, element.Index));
        var alias = element with { Index = new IrVar(element.Loc, index) { Type = indexType } };
        _code.Alias(symbol, alias);
        // An index that steps a variable (`a[i++]`) is no specification; the alias is
        // already in the terms a specification uses.
        _spec.Alias(symbol, !v.Initializer.Value.DescendantNodes().Any(Borrowing.IsStep) &&
            _spec.Lower(v.Initializer.Value) is IrElement se ? se with { Index = alias.Index } : alias);
        return alias;
    }

    /// <summary>
    /// Whether <paramref name="scope"/> may, at a node <paramref name="at"/> accepts, assign
    /// one of the fields in <paramref name="read"/>, or call a method of the class that may.
    /// </summary>
    private bool ChangesFields(SyntaxNode scope, ILocalSymbol symbol, HashSet<ISymbol> read, Func<SyntaxNode, bool> at)
    {
        var self = symbol.ContainingSymbol.ContainingType;
        foreach (var n in scope.DescendantNodes().Where(at))
        {
            if (n is AssignmentExpressionSyntax a && model.GetSymbolInfo(a.Left).Symbol is IFieldSymbol { IsStatic: false } af &&
                read.Contains(af))
                return true;
            if (n is InvocationExpressionSyntax inv &&
                model.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: false, ReturnsByRef: false } m &&
                SymbolEqualityComparer.Default.Equals(m.ContainingType?.OriginalDefinition, self?.OriginalDefinition) &&
                !Declarations.Has(m, known.LemmaAttribute))
                return true;
        }
        return false;
    }

    /// <summary>
    /// R30.16. The nodes of <paramref name="scope"/> that may run while the <c>ref</c> local
    /// <paramref name="symbol"/>, declared by <paramref name="decl"/>, is live: those between
    /// the declaration and its last use, or the end of the last loop in the block around a
    /// use. A use cannot precede the declaration, and a loop around the block declares it
    /// afresh; only a jump could reach an earlier node while it is bound, so with one in
    /// the block, every node.
    /// </summary>
    private Func<SyntaxNode, bool> LiveStretch(SyntaxNode scope, SyntaxNode decl, ILocalSymbol symbol)
    {
        if (scope.DescendantNodes().Any(n => n is GotoStatementSyntax or LabeledStatementSyntax or SwitchStatementSyntax))
            return _ => true;
        var from = decl.Span.End;
        var until = scope.DescendantNodes().OfType<IdentifierNameSyntax>()
            .Where(id => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(id).Symbol, symbol))
            .Select(id => id.AncestorsAndSelf().TakeWhile(a => a != scope)
                .Where(a => a == id || a is WhileStatementSyntax or DoStatementSyntax or ForStatementSyntax or CommonForEachStatementSyntax)
                .Max(a => a.Span.End))
            .DefaultIfEmpty(from).Max();
        return n => n.SpanStart >= from && n.SpanStart < until;
    }

    /// <summary>R30.1, R30.2. The locals PALCS0750 has already refused.</summary>
    private readonly HashSet<ISymbol> _staleReported = new(SymbolEqualityComparer.Default);

    /// <summary>PALCS0750. An alias that may be used while unbound or stale.</summary>
    private IrExpr? StaleAlias(ILocalSymbol symbol, AliasFlow flow)
    {
        var at = flow.Failure ?? symbol.DeclaringSyntaxReferences[0].GetSyntax();
        diagnostics.Error("PALCS0750", Locations.From(at),
            $"`{symbol.Name}` stands for an element or the array of a field, and is rebound, but it may " +
            "be used here before it is bound, or after the field may have changed (an assignment to it, " +
            "or a call that may replace it) without being rebound since; or it is used where the " +
            "rebinding cannot be followed (a lambda, `goto`, `switch`, `try`). Rebind it, by a statement, " +
            "after every such change (doc/translation.md R30.1, R30.2).");
        _staleReported.Add(symbol);
        return null;
    }

    /// <summary>R30.1. <c>Unsafe.NullRef&lt;T&gt;()</c>.</summary>
    private bool IsNullRef(ExpressionSyntax e)
    {
        while (e is ParenthesizedExpressionSyntax p) e = p.Expression;
        return e is InvocationExpressionSyntax { ArgumentList.Arguments.Count: 0 } call &&
               model.GetSymbolInfo(call).Symbol is IMethodSymbol { Name: "NullRef", ContainingType: var t } &&
               t.ToDisplayString() == "System.Runtime.CompilerServices.Unsafe";
    }

    /// <summary>R30.1. The index local of each rebindable <c>ref</c> local.</summary>
    private readonly Dictionary<ISymbol, (string Index, IrType Type)> _refRebinds = new(SymbolEqualityComparer.Default);

    /// <summary>R30.2. The array locals rebound from their field (<c>a = _f;</c>).</summary>
    private readonly HashSet<ISymbol> _fieldRebinds = new(SymbolEqualityComparer.Default);

    /// <summary>
    /// R30.1. A <c>ref</c> local that is declared null (<c>ref Unsafe.NullRef&lt;T&gt;()</c>)
    /// or rebound (<c>r = ref e;</c>), where every binding is an element of the same field's
    /// array, either directly or through the same <c>ref</c>-returning method (R24.9), and
    /// every rebinding is a statement. It is R24.8's element at an index local, which each
    /// rebinding assigns, provided the local is bound, and bound since the field last changed,
    /// wherever it is used (<see cref="AliasFlow"/>). The element is then always the field's
    /// current array at the index, as the reference would be. A null reference is never read:
    /// its index local starts at 0, and the flow check is what makes that value unobservable.
    /// </summary>
    private IrExpr? RebindableRefLocal(VariableDeclaratorSyntax v, ILocalSymbol symbol, SyntaxNode node,
        ExpressionSyntax target, List<AssignmentExpressionSyntax> rebinds, ImmutableArray<IrStmt>.Builder statements)
    {
        static ExpressionSyntax Bare(ExpressionSyntax e)
        {
            while (e is ParenthesizedExpressionSyntax p) e = p.Expression;
            return e;
        }
        var isNull = IsNullRef(target);
        if (rebinds.Any(a => a.Parent is not ExpressionStatementSyntax)) return null;
        var targets = (isNull ? [] : new List<ExpressionSyntax> { Bare(target) })
            .Concat(rebinds.Select(a => Bare(((RefExpressionSyntax)a.Right).Expression))).ToList();
        if (targets.Count == 0) return null;
        ISymbol? Root(ExpressionSyntax e) => e switch
        {
            InvocationExpressionSyntax call => model.GetSymbolInfo(call).Symbol,
            ElementAccessExpressionSyntax { Expression: var arr } => model.GetSymbolInfo(arr).Symbol is IFieldSymbol f ? f : null,
            _ => null,
        };
        var root = Root(targets[0]);
        if (root is null || targets.Any(t => !SymbolEqualityComparer.Default.Equals(Root(t), root))) return null;
        var read = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        if (root is IFieldSymbol rf) read.Add(rf);
        else if (root is IMethodSymbol { DeclaringSyntaxReferences: [var callee] } && callee.SyntaxTree == model.SyntaxTree)
        {
            foreach (var id in callee.GetSyntax().DescendantNodes().OfType<IdentifierNameSyntax>())
                if (model.GetSymbolInfo(id).Symbol is IFieldSymbol f) read.Add(f);
        }
        else return null;
        var scope = node.Parent ?? node;
        var flow = new AliasFlow(model, known, symbol, read,
            e => e.Expression is AssignmentExpressionSyntax a && rebinds.Contains(a));
        if (!flow.Check(scope, node, current: !isNull)) return StaleAlias(symbol, flow);
        var template = isNull ? rebinds[0].Right : v.Initializer!.Value;
        if (_code.Lower(template) is not IrElement element) return null;
        var index = Fresh("ref");
        var indexType = element.Index.Type ?? IrPrim.Int;
        var loc = Locations.From(v);
        statements.Add(new IrLocalDecl(loc, index, indexType,
            isNull ? new IrLiteral(loc, 0) { Type = indexType } : element.Index));
        var alias = element with { Index = new IrVar(element.Loc, index) { Type = indexType } };
        _code.Alias(symbol, alias);
        _spec.Alias(symbol, alias);
        _refRebinds[symbol] = (index, indexType);
        return alias;
    }

    /// <summary>
    /// R5.2a. Whether nothing in <paramref name="scope"/> writes <paramref name="local"/>
    /// after its declaration: no assignment, compound assignment, increment or decrement has
    /// it as its target, and it is never passed by <c>ref</c> or <c>out</c>. Such a local
    /// names one value for its whole life, and is bound as one rather than kept in a cell.
    /// An arithmetic local keeps its cell: its value then reaches the solver as a name
    /// rather than as its initialiser inlined, which arithmetic proofs depend on.
    /// </summary>
    private bool ThroughReference(ExpressionSyntax e) =>
        model.GetTypeInfo(e).Type is { IsReferenceType: true };

    private bool NeverWritten(ILocalSymbol local, SyntaxNode scope)
    {
        foreach (var n in scope.DescendantNodes())
        {
            var target = n switch
            {
                AssignmentExpressionSyntax a => a.Left,
                PrefixUnaryExpressionSyntax u when u.IsKind(SyntaxKind.PreIncrementExpression) ||
                                                   u.IsKind(SyntaxKind.PreDecrementExpression) => u.Operand,
                PostfixUnaryExpressionSyntax u when u.IsKind(SyntaxKind.PostIncrementExpression) ||
                                                    u.IsKind(SyntaxKind.PostDecrementExpression) => u.Operand,
                ArgumentSyntax { RefKindKeyword.RawKind: not (int)SyntaxKind.None } arg => arg.Expression,
                ArgumentSyntax arg when Declarations.WrittenParameterOf(arg, model, known) is not null
                    => arg.Expression,
                RefExpressionSyntax r => r.Expression,
                _ => null,
            };
            // R33.26. A write through a reference (`book._entries[i]`, `ref book._entries[i]`)
            // reaches the heap, not the local that holds the reference.
            while (target is ParenthesizedExpressionSyntax or MemberAccessExpressionSyntax or ElementAccessExpressionSyntax)
                target = target switch
                {
                    ParenthesizedExpressionSyntax p => p.Expression,
                    MemberAccessExpressionSyntax m when !ThroughReference(m.Expression) => m.Expression,
                    ElementAccessExpressionSyntax e when !ThroughReference(e.Expression) => e.Expression,
                    _ => null,
                };
            if (target is IdentifierNameSyntax id &&
                SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(id).Symbol, local))
                return false;
        }
        return true;
    }

    private IrStmt LowerExpressionStatement(ExpressionStatementSyntax node, IrLoc loc)
    {
        // R33.17. `a = _field;` re-reading a field alias: `a` already is the field.
        if (_resyncs.Contains(node)) return new IrBlock(loc, ImmutableArray<IrStmt>.Empty);
        // R30.33. The replacement of a field whose old array a local keeps.
        if (_keepers.TryGetValue(node, out var kept)) return KeepAndReplace(node, kept, loc);
        // R33.18. A call of a method that does nothing.
        if (node.Expression is InvocationExpressionSyntax call && DoesNothing(call))
            return new IrBlock(loc, ImmutableArray<IrStmt>.Empty);
        return LowerSideEffect(node.Expression, loc);
    }

    /// <summary>R33.17. The statements <c>a = _field;</c> that re-read a field alias.</summary>
    private readonly HashSet<SyntaxNode> _resyncs = [];

    /// <summary>R33.17. The field each R24.19 alias names.</summary>
    private readonly Dictionary<ISymbol, IFieldSymbol> _fieldAliases = new(SymbolEqualityComparer.Default);

    /// <summary>
    /// R33.18. A call, as a statement, of a non-virtual source method whose body, as
    /// compiled (after preprocessing), is empty and that carries no contract, with arguments
    /// that are variables, constants or fields, passed by value. Running it changes nothing,
    /// and it returns.
    /// </summary>
    private bool DoesNothing(InvocationExpressionSyntax call)
    {
        if (model.GetSymbolInfo(call).Symbol is not IMethodSymbol m) return false;
        m = m.OriginalDefinition;
        if (m.IsVirtual || m.IsAbstract || m.IsOverride || m.IsExtern || m.IsPartialDefinition) return false;
        if (m.DeclaringSyntaxReferences is not [var decl] ||
            decl.GetSyntax() is not MethodDeclarationSyntax { Body.Statements.Count: 0, ExpressionBody: null } md)
            return false;
        if (known.IsPalIntrinsic(m) ||
            md.AttributeLists.SelectMany(l => l.Attributes).Any(a =>
                a.Name.ToString() is "Requires" or "Ensures" or "Throws" or "Lemma" or "Spec" or "PulseBody" or "Pure"))
            return false;
        if (call.Expression is MemberAccessExpressionSyntax { Expression: not ThisExpressionSyntax }) return false;
        // An argument under a conversion is lowered for its diagnostics (R17.7's borrow).
        return call.ArgumentList.Arguments.All(arg =>
            arg.RefKindKeyword.IsKind(SyntaxKind.None) &&
            model.GetConversion(arg.Expression).IsIdentity &&
            arg.Expression is IdentifierNameSyntax or LiteralExpressionSyntax
                or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax });
    }

    /// <summary>
    /// R33.17. Whether calling <paramref name="method"/> may replace <paramref name="field"/>
    /// of the receiver: its body, or a body it calls on the receiver, assigns the field or
    /// passes it by reference. A method without a body here, or one an override could
    /// replace, may.
    /// </summary>
    private bool MayReplace(IMethodSymbol method, IFieldSymbol field, HashSet<IMethodSymbol> seen)
    {
        method = method.OriginalDefinition;
        if (!seen.Add(method)) return false;
        if (Declarations.Has(method, known.LemmaAttribute) || known.IsPalIntrinsic(method)) return false;
        if ((method.IsVirtual || method.IsAbstract || method.IsOverride) && method.ContainingType is not { IsSealed: true })
            return true;
        if (method.DeclaringSyntaxReferences is not [var decl]) return true;
        var body = decl.GetSyntax();
        var calleeModel = model.Compilation.GetSemanticModel(body.SyntaxTree);
        foreach (var n in body.DescendantNodes())
        {
            if (n is AttributeListSyntax) continue;
            if (n is AssignmentExpressionSyntax a &&
                SymbolEqualityComparer.Default.Equals(calleeModel.GetSymbolInfo(a.Left).Symbol?.OriginalDefinition, field.OriginalDefinition))
                return true;
            if (n is ArgumentSyntax { RefKindKeyword.RawKind: not (int)SyntaxKind.None } arg &&
                SymbolEqualityComparer.Default.Equals(calleeModel.GetSymbolInfo(arg.Expression).Symbol?.OriginalDefinition, field.OriginalDefinition))
                return true;
            if (n is InvocationExpressionSyntax inv &&
                calleeModel.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: false } m &&
                SymbolEqualityComparer.Default.Equals(m.ContainingType?.OriginalDefinition, field.ContainingType.OriginalDefinition) &&
                (inv.Expression is IdentifierNameSyntax or GenericNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }) &&
                MayReplace(m, field, seen))
                return true;
            // A call on another object of the class could reach this one only through a
            // reference to it, which the class's own methods do not take.
        }
        return false;
    }

    /// <summary>R33.17. Whether <paramref name="n"/> may replace <paramref name="field"/>.</summary>
    private bool Replaces(SyntaxNode n, IFieldSymbol field) => n switch
    {
        AssignmentExpressionSyntax a =>
            SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol?.OriginalDefinition, field.OriginalDefinition),
        ArgumentSyntax { RefKindKeyword.RawKind: not (int)SyntaxKind.None } arg =>
            SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(arg.Expression).Symbol?.OriginalDefinition, field.OriginalDefinition),
        InvocationExpressionSyntax inv when
            model.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: false, ReturnsByRef: false } m &&
            SymbolEqualityComparer.Default.Equals(m.ContainingType?.OriginalDefinition, field.ContainingType.OriginalDefinition) &&
            !Declarations.Has(m, known.LemmaAttribute) =>
            MayReplace(m, field, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default)),
        _ => false,
    };

    /// <summary>
    /// Lowers an expression evaluated for its effect. A <c>for</c> loop's initialisers
    /// and incrementors are such expressions without being statements, so this is
    /// shared rather than reached by synthesising an <c>ExpressionStatement</c> — a
    /// synthesised node is not in the syntax tree, and the semantic model rejects it.
    /// </summary>
    private IrStmt LowerSideEffect(ExpressionSyntax expression, IrLoc loc)
    {
        switch (expression)
        {
            case AssignmentExpressionSyntax assign:
                return LowerAssignment(assign, loc);

            // `i++` / `++i` / `i--` / `--i` are assignments (R5.3); the value they
            // produce is discarded in statement position, so no temporary is needed.
            case PostfixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.PostIncrementExpression } p:
                return Step(p.Operand, BinOp.Add, loc);
            case PostfixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.PostDecrementExpression } p:
                return Step(p.Operand, BinOp.Sub, loc);
            case PrefixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.PreIncrementExpression } p:
                return Step(p.Operand, BinOp.Add, loc);
            case PrefixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.PreDecrementExpression } p:
                return Step(p.Operand, BinOp.Sub, loc);

            case InvocationExpressionSyntax call:
                return RefFieldCopy(call, loc) ?? RefElementCopy(call, loc) ?? LowerCallStatement(call, loc);

            case ConditionalAccessExpressionSyntax access
                when known.IsRegionClass(model.GetTypeInfo(access.Expression).Type):
                return LowerRegionConditionalAccess(access, loc);

            default:
                return UnsupportedStatement(expression, loc);
        }
    }

    /// <summary>
    /// R27.29. <c>x?.M();</c> and <c>x?.F = v;</c> on a region pointer, as statements, are
    /// <c>if (x != null) { x.M(); }</c> and <c>if (x != null) { x.F = v; }</c>. A pointer is
    /// a value (R27.3), so the test and the member read the same <c>x</c>; an <c>x</c> with an
    /// effect would be evaluated twice, and is refused.
    /// </summary>
    private IrStmt LowerRegionConditionalAccess(ConditionalAccessExpressionSyntax node, IrLoc loc)
    {
        var subject = _code.Lower(node.Expression);
        if (ExprLowerer.HasEffect(subject) || subject.Type is not IrClassType pointer)
            return UnsupportedStatement(node, loc);
        var bound = subject with { Type = pointer with { Nullable = false } };
        var body = _code.WithBound(bound, node.Expression, () => LowerSideEffect(node.WhenNotNull, loc));
        var test = new IrBinary(loc, BinOp.Ne, subject, new IrNull(loc) { Type = pointer with { Nullable = true } })
        {
            Type = IrPrim.Bool,
        };
        return new IrIf(loc, test, body, null);
    }

    private IrStmt Step(ExpressionSyntax target, BinOp op, IrLoc loc)
    {
        // R5.3 expands `x++` into `x = x + 1`, which names the L-value twice. C# evaluates
        // it once, so anything effectful in it is hoisted first and both copies share it.
        var lowered = _code.LinearizeLValue(_code.Lower(target), out var prelude);
        // R24.16: the one is at the target's type, so `u++` on a `uint` adds `1ul`.
        var one = lowered.Type is IrPrim { IsMachineInt: true } prim
            ? new IrLiteral(loc, 1) { Type = prim } : new IrLiteral(loc, 1);
        var assign = new IrAssign(loc, lowered, new IrBinary(loc, op, lowered, one)
            { Wraps = _code.Wraps(target), Type = lowered.Type });
        return prelude.IsEmpty ? assign : new IrBlock(loc, [.. prelude, assign]);
    }

    private IrStmt LowerAssignment(AssignmentExpressionSyntax node, IrLoc loc)
    {
        // R30.29. Rebinding a snapshot.
        if (node.IsKind(SyntaxKind.SimpleAssignmentExpression) &&
            node.Right is RefExpressionSyntax { Expression: var snapshotTarget } &&
            model.GetSymbolInfo(node.Left).Symbol is ILocalSymbol snapshotLocal &&
            _snapshotLocals.TryGetValue(snapshotLocal, out var snapshotType))
            return new IrAssign(loc, new IrVar(loc, snapshotLocal.Name) { Type = snapshotType },
                SnapshotTarget(snapshotTarget, snapshotType));
        // R30.1, R30.2. Rebinding an alias: a `ref` local's index, or nothing at all.
        if (model.GetSymbolInfo(node.Left).Symbol is ILocalSymbol rebound)
        {
            if (node.Right is RefExpressionSyntax && _refRebinds.TryGetValue(rebound, out var rb))
            {
                if (_code.Lower(node.Right) is IrElement el)
                    return new IrAssign(loc, new IrVar(loc, rb.Index) { Type = rb.Type }, el.Index);
                return UnsupportedStatement(node, loc);
            }
            if (_fieldRebinds.Contains(rebound) && node.IsKind(SyntaxKind.SimpleAssignmentExpression))
                return new IrBlock(loc, []);
        }
        // Compound assignment `x op= e` is `x = x op e` (R5.3).
        var op = node.Kind() switch
        {
            SyntaxKind.SimpleAssignmentExpression => (BinOp?)null,
            SyntaxKind.AddAssignmentExpression => BinOp.Add,
            SyntaxKind.SubtractAssignmentExpression => BinOp.Sub,
            SyntaxKind.MultiplyAssignmentExpression => BinOp.Mul,
            SyntaxKind.DivideAssignmentExpression => BinOp.Div,
            SyntaxKind.ModuloAssignmentExpression => BinOp.Rem,
            SyntaxKind.AndAssignmentExpression => BinOp.BitAnd,
            SyntaxKind.OrAssignmentExpression => BinOp.BitOr,
            SyntaxKind.ExclusiveOrAssignmentExpression => BinOp.BitXor,
            SyntaxKind.LeftShiftAssignmentExpression => BinOp.Shl,
            SyntaxKind.RightShiftAssignmentExpression => BinOp.Shr,
            // Every other assignment operator — `??=`, `>>>=` — is outside the subset.
            // It reaches here like any other statement, so it is refused like any other:
            // §18's totality is a property of the frontend, not of the operators it knows.
            _ => null,
        };

        // R33.11. `x ??= d;` on a local or parameter is `x = x ?? d;`: for a comparer, whose
        // null the model cannot see, `is_null x ? d : x` (R25.4); for an `option`,
        // `Some? x ? x : Some d`.
        if (node.IsKind(SyntaxKind.CoalesceAssignmentExpression) &&
            model.GetSymbolInfo(node.Left).Symbol is ILocalSymbol { IsRef: false } or IParameterSymbol { RefKind: RefKind.None } &&
            _code.Lower(node.Left) is { Type: { } coalescedType } coalesced && !ExprLowerer.HasEffect(coalesced))
        {
            if (Sorted.IsComparer(coalescedType))
                return new IrAssign(loc, coalesced,
                    new IrConditional(loc, Sorted.IsNull(loc, coalesced), _code.Lower(node.Right), coalesced)
                        { Type = coalescedType });
            if (coalescedType is IrOptionType && _code.Lower(node.Right) is { Type: { } fallbackType } fallback)
                return new IrAssign(loc, coalesced,
                    new IrConditional(loc,
                        new IrOptionOp(loc, OptionOpKind.HasValue, coalesced) { Type = IrPrim.Bool },
                        coalesced,
                        fallbackType is IrOptionType
                            ? fallback
                            : new IrOptionOp(loc, OptionOpKind.Some, fallback) { Type = coalescedType })
                        { Type = coalescedType });
        }

        if (op is null && !node.IsKind(SyntaxKind.SimpleAssignmentExpression))
        {
            diagnostics.Unsupported(loc, $"The assignment operator `{node.OperatorToken}`");
            return new IrBlock(loc, []);
        }

        // R26.8. `(a, b) = e` reads `e` once and assigns its components left to right.
        if (op is null && node.Left is TupleExpressionSyntax { Arguments.Count: 2 } targets &&
            _code.Lower(node.Right) is { Type: IrUserSpecType { FStar: WellKnown.TupleType } pairType } pairValue)
        {
            var name = Fresh("pair");
            var pair = new IrVar(loc, name) { Type = pairType };
            return new IrBlock(loc,
            [
                new IrLocalDecl(loc, name, pairType, pairValue) { Immutable = true },
                new IrAssign(loc, _code.Lower(targets.Arguments[0].Expression),
                    new IrSpecOp(loc, "fst", [pair]) { MachineArgs = true, Type = pairType.Args[0] }),
                new IrAssign(loc, _code.Lower(targets.Arguments[1].Expression),
                    new IrSpecOp(loc, "snd", [pair]) { MachineArgs = true, Type = pairType.Args[1] }),
            ]);
        }

        // R33.5. Rebinding a rebound `ref` local assigns its index.
        if (op is null && node.Right is RefExpressionSyntax { Expression: var rebind } &&
            model.GetSymbolInfo(node.Left).Symbol is { } reboundSymbol &&
            _rebound.TryGetValue(reboundSymbol, out var reboundIndex) &&
            _code.Lower(rebind) is IrElement reboundElement)
            return new IrAssign(loc, reboundIndex, _code.ToDeclared(reboundElement.Index, IrPrim.Int));

        if (_code.SpecIndexerWrite(node, loc) is { } indexerWrite) return indexerWrite;
        if (_code.ComputedWrite(node, loc) is { } setterCall) return new IrExprStmt(loc, setterCall);

        var target = _code.Lower(node.Left);
        var value = _code.Lower(node.Right);

        if (op is null) return new IrAssign(loc, target, _code.ToDeclared(value, target.Type));

        var linear = _code.LinearizeLValue(target, out var prelude);
        var assign = new IrAssign(loc, linear, new IrBinary(loc, op.Value, linear, value)
            { Wraps = _code.Wraps(node.Left) });
        return prelude.IsEmpty ? assign : new IrBlock(loc, [.. prelude, assign]);
    }

    /// <summary>
    /// A call in statement position is either a proof-annotation intrinsic, a
    /// <c>[Lemma]</c> application, or an ordinary method call.
    /// </summary>
    /// <summary>
    /// R23.11. <c>M(ref f)</c>, where <c>f</c> is a scalar field of the receiver and <c>M</c> an
    /// instance method of the same class called on it, whose body neither names <c>f</c> nor
    /// calls anything: the call is <c>{ var t = f; M(ref t); f = t; }</c>. A by-reference
    /// argument is a cell (R6.10) and a field is not one; copying in and out is the same
    /// program because <c>M</c> can observe <c>f</c> only through its parameter.
    /// </summary>
    private IrStmt? RefFieldCopy(InvocationExpressionSyntax node, IrLoc loc)
    {
        if (model.GetSymbolInfo(node).Symbol is not IMethodSymbol { IsStatic: false, MethodKind: MethodKind.Ordinary } method)
            return null;
        if (node.Expression is not (IdentifierNameSyntax or
            MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }))
            return null;
        var refs = node.ArgumentList.Arguments
            .Select((a, i) => (Arg: a, Index: i))
            .Where(x => x.Arg.RefKindKeyword.IsKind(SyntaxKind.RefKeyword))
            .ToList();
        if (refs is not [var (arg, _)]) return null;
        if (arg.Expression is not (IdentifierNameSyntax or
            MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }))
            return null;
        if (model.GetSymbolInfo(arg.Expression).Symbol is not IFieldSymbol { IsStatic: false } field ||
            !SymbolEqualityComparer.Default.Equals(field.ContainingType.OriginalDefinition,
                method.ContainingType.OriginalDefinition) ||
            !field.Type.IsValueType || known.MapType(field.Type) is not IrPrim fieldType)
            return null;
        if (method.DeclaringSyntaxReferences is not [var decl]) return null;
        var body = decl.GetSyntax();
        var calleeModel = model.Compilation.GetSemanticModel(body.SyntaxTree);
        foreach (var n in body.DescendantNodes())
        {
            if (n is InvocationExpressionSyntax inv &&
                !(inv.Expression is IdentifierNameSyntax { Identifier.ValueText: "nameof" }))
                return null;
            if (n is IdentifierNameSyntax id &&
                SymbolEqualityComparer.Default.Equals(calleeModel.GetSymbolInfo(id).Symbol?.OriginalDefinition,
                    field.OriginalDefinition))
                return null;
        }

        var lowered = LowerCallStatement(node, loc);
        if (lowered is not IrExprStmt { Expr: IrCall call }) return lowered;
        var temp = Fresh("ref");
        var cell = new IrVar(loc, temp) { Type = fieldType };
        var target = _code.Lower(arg.Expression);
        var args = call.Args.Select(a => a is IrRefArg { Operand: IrField } r ? r with { Operand = cell } : a)
            .ToImmutableArray();
        return new IrBlock(loc,
        [
            new IrLocalDecl(loc, temp, fieldType, target),
            new IrExprStmt(loc, call with { Args = args }),
            new IrAssign(loc, target, cell),
        ]);
    }

    /// <summary>
    /// R33.16. <c>M(ref a[i])</c>, or <c>M(ref x)</c> for a <c>ref</c> local <c>x</c> into
    /// <c>a[i]</c> (R24.8/R33.5), where the element is a struct, <c>a</c> and <c>i</c> are
    /// locals, parameters or fields, and <c>M</c> is isolated from the element: neither it nor
    /// anything it calls names an array of the element type, throws, or fails to return. The
    /// call is <c>{ var t = a[i]; M(ref t); a[i] = t; }</c>: <c>M</c> can observe and change
    /// the element only through its parameter, and runs to completion, so the element holds
    /// what the parameter held at the end, as it would have all along.
    /// </summary>
    private IrStmt? RefElementCopy(InvocationExpressionSyntax node, IrLoc loc)
    {
        if (model.GetSymbolInfo(node).Symbol is not IMethodSymbol method) return null;
        var refs = node.ArgumentList.Arguments
            .Where(a => a.RefKindKeyword.IsKind(SyntaxKind.RefKeyword))
            .ToList();
        if (refs is not [var arg]) return null;
        if (model.GetTypeInfo(arg.Expression).Type is not { IsValueType: true } elementType ||
            known.MapType(elementType) is not { } mapped)
            return null;
        if (!Isolated(method, elementType, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default)))
            return null;
        var lowered = LowerCallStatement(node, loc);
        if (lowered is not IrExprStmt { Expr: IrCall call }) return null;
        if (call.Args.Count(a => a is IrRefArg) != 1 ||
            call.Args.FirstOrDefault(a => a is IrRefArg) is not IrRefArg { Operand: IrElement element } ||
            element.Array is not (IrVar or IrField { Receiver: IrVar }) ||
            element.Index is not (IrVar or IrLiteral))
            return null;
        var temp = Fresh("ref");
        var cell = new IrVar(loc, temp) { Type = mapped };
        var args = call.Args.Select(a => a is IrRefArg r ? r with { Operand = cell } : a).ToImmutableArray();
        return new IrBlock(loc,
        [
            new IrLocalDecl(loc, temp, mapped, element),
            new IrExprStmt(loc, call with { Args = args }),
            new IrAssign(loc, element, cell),
        ]);
    }

    /// <summary>R33.16. Whether <paramref name="method"/>'s body, and every body it calls, is isolated from arrays of <paramref name="element"/>.</summary>
    private bool Isolated(IMethodSymbol method, ITypeSymbol element, HashSet<IMethodSymbol> seen)
    {
        method = method.OriginalDefinition;
        if (!seen.Add(method)) return true;
        if (method.GetAttributes().Any(a => a.AttributeClass?.Name == "DoesNotReturnAttribute")) return false;
        if (method.DeclaringSyntaxReferences is not [var decl]) return false;
        var body = decl.GetSyntax();
        var calleeModel = model.Compilation.GetSemanticModel(body.SyntaxTree);
        foreach (var n in body.DescendantNodes())
        {
            if (n is AttributeListSyntax) continue;
            if (n is ThrowStatementSyntax or ThrowExpressionSyntax) return false;
            if (n is ExpressionSyntax e && n.Ancestors().All(x => x is not AttributeSyntax) &&
                calleeModel.GetTypeInfo(e).Type is IArrayTypeSymbol at &&
                SymbolEqualityComparer.Default.Equals(at.ElementType.OriginalDefinition, element.OriginalDefinition))
                return false;
            if (n is InvocationExpressionSyntax inv &&
                !(inv.Expression is IdentifierNameSyntax { Identifier.ValueText: "nameof" }))
            {
                if (calleeModel.GetSymbolInfo(inv).Symbol is not IMethodSymbol m) return false;
                if (known.IsPalIntrinsic(m) || Declarations.Has(m, known.LemmaAttribute) ||
                    m.GetAttributes().Any(a => a.AttributeClass?.Name == "ConditionalAttribute"))
                    continue;
                if (!Isolated(m, element, seen)) return false;
            }
        }
        return true;
    }

    private IrStmt LowerCallStatement(InvocationExpressionSyntax node, IrLoc loc)
    {
        if (!_code.ArgumentsInOrder(node.ArgumentList)) return new IrBlock(loc, []);
        if (model.GetSymbolInfo(node).Symbol is not IMethodSymbol method)
            return UnsupportedStatement(node, loc);

        var args = node.ArgumentList.Arguments;

        if (known.IsPalIntrinsic(method))
        {
            switch (method.Name)
            {
                case nameof(PalLang.Pal.Assert):
                    return new IrGhostStmt(loc, GhostKind.Assert, _spec.Lower(args[0].Expression), null);
                case nameof(PalLang.Pal.Assume):
                    return new IrGhostStmt(loc, GhostKind.Assume, _spec.Lower(args[0].Expression), null);
                // R30.36. Attached to the `if` before it by Normalize.
                case nameof(PalLang.Pal.Join):
                    return new IrGhostStmt(loc, GhostKind.Join, _spec.Lower(args[0].Expression), null);
                // R30.39. Likewise.
                case nameof(PalLang.Pal.Split):
                    return new IrGhostStmt(loc, GhostKind.Split, null, null);
                // R27.48. The rest of the block is dropped by LowerBlock.
                case nameof(PalLang.Pal.Unreachable):
                    return new IrGhostStmt(loc, GhostKind.Unreachable, null, null);
                case nameof(PalLang.Pal.GhostStmt) when _spec.ConstantString(args[0].Expression) is { } text:
                    return new IrGhostStmt(loc, GhostKind.Raw, null, text);
                // R5.13. The argument is lowered as an ordinary expression so that the
                // name it mentions counts as live in an enclosing loop; what it may be is
                // decided by the emitter, which is where the slot kinds are known.
                case nameof(PalLang.Pal.Share):
                    return new IrGhostStmt(loc, GhostKind.Share, _spec.Lower(args[0].Expression), null);
                case nameof(PalLang.Pal.Gather):
                    return new IrGhostStmt(loc, GhostKind.Gather, _spec.Lower(args[0].Expression), null);
                // R17.6. The end of a borrow. Lowered the same way, and for the same
                // reason: which of the three receipts is being redeemed depends on how the
                // span was created, and that is recorded on its slot, which only the
                // emitter has.
                case nameof(PalLang.Pal.Restore):
                    return new IrGhostStmt(loc, GhostKind.Restore, _spec.Lower(args[0].Expression), null);
                // `Invariant`, `Decreases` and `Requires`/`Ensures` are consumed by the
                // enclosing construct, not emitted here; see ExtractLoopSpecs.
                case nameof(PalLang.Pal.Invariant):
                case nameof(PalLang.Pal.Decreases):
                case nameof(PalLang.Pal.Requires):
                case nameof(PalLang.Pal.Ensures):
                    return new IrBlock(loc, []);
                default:
                    diagnostics.Unsupported(loc, $"`Pal.{method.Name}` in statement position");
                    return new IrBlock(loc, []);
            }
        }

        // Model Release C#: Conditional("DEBUG") removes the whole call, including
        // argument evaluation. Use Pal.Assert for an assertion that verification checks.
        if (method is { Name: "Assert" or "Fail", IsStatic: true } &&
            method.ContainingType.ToDisplayString() == "System.Diagnostics.Debug")
            return new IrBlock(loc, []);

        // R23.2, R25.7. The BCL's argument guards are the `if … throw` they abbreviate.
        if (ArgumentGuard(method, args, loc) is { } guard)
            return guard;

        // R22.20 and R22.25. The bulk operations of `System.Array` on one-dimensional
        // arrays. Arguments are matched to parameters by name, so `length:` and the like
        // need no special treatment.
        if (method is { IsStatic: true } &&
            method.ContainingType?.SpecialType == SpecialType.System_Array &&
            ArrayBulkOp(method, args, loc) is { } bulk)
            return bulk;

        // R23.4. `Array.Resize(ref a, n)` replaces `a` by a fresh array of length `n`.
        if (method is { IsStatic: true, Name: "Resize", IsGenericMethod: true } &&
            method.ContainingType?.SpecialType == SpecialType.System_Array && args.Count == 2 &&
            args[0].RefKindKeyword.IsKind(SyntaxKind.RefKeyword) &&
            model.GetTypeInfo(args[0].Expression).Type is IArrayTypeSymbol { Rank: 1 } resized &&
            known.MapType(resized) is IrArrayType resizedType)
        {
            // R26.8. A tuple's components are defaulted too.
            foreach (var rtp in WellKnown.DefaultedIn(resized.ElementType))
                _code.DefaultedTypeParameters.Add(rtp.Name);
            var target = _code.Lower(args[0].Expression);
            return new IrAssign(loc, target,
                new IrNewArray(loc, resizedType.Element, _code.Lower(args[1].Expression))
                { Source = target, Type = resizedType });
        }
        // R26.1. A callable delegate is a pure function (trusted), so a call evaluated only
        // for its effect has none the proof can see: its arguments are evaluated, and the
        // result, `()` for an `Action`, is dropped.
        if (method.MethodKind == MethodKind.DelegateInvoke &&
            known.MapType(method.ContainingType) is IrDelegateType { Callable: true } dlg)
            return new IrLocalDecl(loc, $"__pal_discard_{_discards++}", dlg.Return!, _code.Lower(node)) { Immutable = true };

        // R27.22. A `void` region operation is a library lemma, called as a ghost statement.
        // R27.40. So is a `void` spec operation.
        if ((known.RegionOpName(method) is not null || known.SpecOpName(method) is not null) && method.ReturnsVoid)
            return new IrGhostStmt(loc, GhostKind.LemmaCall, _spec.Lower(node), null);

        var kind = Declarations.KindOf(method, known);
        if (kind == CalleeKind.Lemma)
        {
            var call = new IrCall(loc, Naming.Of(method), [.. args.Select(a => _spec.Lower(a.Expression))])
            {
                Kind = CalleeKind.Lemma,
                ParamTypes = Declarations.ParamTypes(method, known, receiver: false),
                TypeArguments = known.TypeArguments(method),
            };
            return new IrGhostStmt(loc, GhostKind.LemmaCall, call, null);
        }

        // A call in statement position is the same call it would be in expression
        // position, so it is lowered by the same code: the receiver threading of §4.5 and
        // the `MutatesReceiver` flag of R4.11 are decided in exactly one place.
        if (kind == CalleeKind.Method) return new IrExprStmt(loc, _code.Lower(node));

        diagnostics.Unsupported(loc, $"A call to `{method.Name}`");
        return new IrBlock(loc, []);
    }

    private IrStmt LowerWhile(WhileStatementSyntax node, IrLoc loc) => AfterLoop(() =>
    {
        var (invariants, decreases, body) = ExtractLoopSpecs(node.Statement);
        var cond = _code.Lower(node.Condition);
        // R26.11. A guard that writes -- `(i = f(n)) < size`, `++i < bound` -- is a `for`
        // whose init and step are the write: the guard's effect runs before each test, the
        // loop specification describes the state just after it, and a `continue` still
        // runs it (R5.7).
        if (HoistGuardEffect(cond) is var (effect, test))
            return new IrFor(loc, effect, test, effect, invariants, decreases, body);
        return new IrWhile(loc, cond, invariants, decreases, body);
    }, loc);

    /// <summary>
    /// R27.54. <c>do S while (c);</c> is <c>while (true) { S; if (!c) break; }</c>: the body
    /// runs before the first test, and the loop's specification describes the state at the
    /// top of the body, as it does for a <c>while</c>. A <c>continue</c> would skip the test,
    /// so one aimed at this loop is refused.
    /// </summary>
    private IrStmt LowerDo(DoStatementSyntax node, IrLoc loc)
    {
        if (node.Statement.DescendantNodesAndSelf(n => n == node.Statement ||
                n is not (WhileStatementSyntax or DoStatementSyntax or ForStatementSyntax or ForEachStatementSyntax or
                          AnonymousFunctionExpressionSyntax or LocalFunctionStatementSyntax))
                .OfType<ContinueStatementSyntax>().FirstOrDefault() is { } cont)
        {
            diagnostics.Unsupported(Locations.From(cont), "A `continue` in a `do` loop",
                "pal-csharp translates `do S while (c)` as `while (true) { S; if (!c) break; }` " +
                "(doc/translation.md R27.54), where a `continue` would skip the test.");
            return new IrBlock(loc, []);
        }
        return AfterLoop(() =>
        {
            var (invariants, decreases, body) = ExtractLoopSpecs(node.Statement);
            var test = new IrIf(loc, new IrUnary(loc, UnOp.Not, _code.Lower(node.Condition)) { Type = IrPrim.Bool },
                new IrBreak(loc), null);
            var stmts = body is IrBlock b ? b.Statements : [body];
            return new IrWhile(loc, new IrLiteral(loc, true) { Type = IrPrim.Bool }, invariants, decreases,
                new IrBlock(loc, [.. stmts, test]));
        }, loc);
    }

    /// <summary>
    /// R26.11. Splits a guard whose leftmost operand is an effectful expression ending in
    /// a snapshot of the value it wrote into the writes and the effect-free test. Only the
    /// shapes in which that is exact are split: the snapshot is the last thing the prelude
    /// does, so it equals the cell it copies; and the rest of the guard reads nothing the
    /// prelude could change before the test would have.
    /// </summary>
    private static (ImmutableArray<IrStmt> Effect, IrExpr Test)? HoistGuardEffect(IrExpr cond)
    {
        static (ImmutableArray<IrStmt>, IrExpr)? Split(IrExpr e) =>
            e is IrStmtExpr { Prelude: [.. var writes, IrLocalDecl { Init: { } copied } snap], Value: IrVar v } &&
            v.Name == snap.Name && copied is IrVar &&
            writes.All(w => w is IrAssign { Target: IrVar })
                ? ([.. writes], copied)
                : null;

        // An effect-free operand that reads none of the written locals: a literal, another
        // local, an array's length, arithmetic over those.
        static bool Untouched(IrExpr e, ImmutableHashSet<string> written) => e switch
        {
            IrLiteral => true,
            IrVar v => !written.Contains(v.Name),
            IrLength l => Untouched(l.Array, written),
            IrConvert c => Untouched(c.Operand, written),
            IrUnary u => Untouched(u.Operand, written),
            IrBinary b => Untouched(b.Left, written) && Untouched(b.Right, written),
            _ => false,
        };

        switch (cond)
        {
            case IrBinary { Op: BinOp.Lt or BinOp.Le or BinOp.Gt or BinOp.Ge or BinOp.Eq or BinOp.Ne } b
                when Split(b.Left) is var (effect, value) &&
                     Untouched(b.Right, [.. effect.Select(w => ((IrVar)((IrAssign)w).Target).Name)]):
                return (effect, b with { Left = value });
            default:
                return Split(cond) is var (e2, v2) ? (e2, v2) : null;
        }
    }

    private IrStmt LowerFor(ForStatementSyntax node, IrLoc loc) => AfterLoop(() => LowerForInner(node, loc), loc);

    private IrStmt LowerForInner(ForStatementSyntax node, IrLoc loc)
    {
        var init = ImmutableArray.CreateBuilder<IrStmt>();
        if (node.Declaration is { } decl)
        {
            foreach (var v in decl.Variables)
            {
                var symbol = model.GetDeclaredSymbol(v) as ILocalSymbol;
                var type = known.MapType(symbol?.Type);
                if (type is null)
                {
                    diagnostics.Unsupported(Locations.From(v), $"The loop variable type `{decl.Type}`");
                    continue;
                }
                init.Add(new IrLocalDecl(Locations.From(v), v.Identifier.ValueText, type,
                    v.Initializer is null ? null : _code.ToDeclared(_code.Lower(v.Initializer.Value), type)));
            }
        }
        foreach (var e in node.Initializers)
            init.Add(LowerSideEffect(e, Locations.From(e)));

        var step = ImmutableArray.CreateBuilder<IrStmt>();
        foreach (var e in node.Incrementors)
            step.Add(LowerSideEffect(e, Locations.From(e)));

        var (invariants, decreases, body) = ExtractLoopSpecs(node.Statement);

        return new IrFor(loc, init.ToImmutable(),
            node.Condition is null ? null : _code.Lower(node.Condition),
            step.ToImmutable(), invariants, decreases, body);
    }

    /// <summary>
    /// R20.5. <c>foreach (var x in c) body</c>, over an array or list <c>c</c> named by a
    /// local or a parameter, is the counted loop
    /// <c>for (int x__index = 0; x__index &lt; c.Length; x__index++) { var x = c[x__index]; body }</c>.
    /// The counter's range is an invariant of its own, and <c>Pal.Index(x)</c> names it.
    /// </summary>
    private IrStmt LowerForEach(ForEachStatementSyntax node, IrLoc loc) => AfterLoop(() => LowerForEachInner(node, loc), loc);

    private IrStmt LowerForEachInner(ForEachStatementSyntax node, IrLoc loc)
    {
        var collectionType = model.GetTypeInfo(node.Expression).Type;
        var symbol = model.GetSymbolInfo(node.Expression).Symbol;
        if (known.MapType(collectionType) is not IrArrayType && ForEachOwner(node, loc) is { } overOwner)
            return overOwner;
        if (known.MapType(collectionType) is not IrArrayType { Element: var element } arrayType ||
            node.Expression is not IdentifierNameSyntax collection ||
            symbol is not (ILocalSymbol or IParameterSymbol))
        {
            diagnostics.Error("PALCS0620", Locations.From(node.Expression),
                $"`foreach` over `{node.Expression}`. Only an array or a list held in a local " +
                "or a parameter is iterated (doc/translation.md R20.5).");
            return new IrBlock(loc, []);
        }

        // C# forbids changing a list while it is enumerated, and this desugaring would
        // silently tolerate it; so would reassigning the variable that names it.
        if (node.Statement.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a =>
                a.Left is IdentifierNameSyntax { Identifier.ValueText: var n } &&
                n == collection.Identifier.ValueText))
        {
            diagnostics.Error("PALCS0620", Locations.From(node.Expression),
                $"`{collection}` is assigned inside the `foreach` that iterates it " +
                "(doc/translation.md R20.5).");
            return new IrBlock(loc, []);
        }

        var name = node.Identifier.ValueText;
        var index = ExprLowerer.ForEachIndex(name);
        var vloc = Locations.From(node.Identifier);
        IrExpr Index() => new IrVar(vloc, index) { Type = IrPrim.Int };
        IrExpr Coll() => new IrVar(vloc, collection.Identifier.ValueText) { Type = arrayType };
        IrExpr Length() => new IrLength(vloc, Coll()) { Type = IrPrim.Int };
        IrExpr Zero() => new IrLiteral(vloc, 0) { Type = IrPrim.Int };

        var range = new IrBinary(vloc, BinOp.And,
            new IrBinary(vloc, BinOp.Le, Zero(), Index()) { Type = IrPrim.Bool },
            new IrBinary(vloc, BinOp.Le, Index(), Length()) { Type = IrPrim.Bool }) { Type = IrPrim.Bool };

        var (invariants, decreases, body) = ExtractLoopSpecs(node.Statement);
        var first = new IrLocalDecl(vloc, name, element,
            new IrElement(vloc, Coll(), Index()) { Type = element }) { Immutable = true };
        var step = new IrAssign(vloc, Index(),
            new IrBinary(vloc, BinOp.Add, Index(), new IrLiteral(vloc, 1) { Type = IrPrim.Int }) { Type = IrPrim.Int });

        return new IrFor(loc,
            [new IrLocalDecl(vloc, index, IrPrim.Int, Zero())],
            new IrBinary(vloc, BinOp.Lt, Index(), Length()) { Type = IrPrim.Bool },
            [step], [range, .. invariants], decreases,
            new IrBlock(body.Loc, [first, .. ((IrBlock)body).Statements]));
    }

    /// <summary>
    /// R27.51. <c>foreach (T x in o) body</c>, where <c>o</c> is <c>this</c> or a parameter
    /// of an owner class whose <c>GetEnumerator()</c> returns a borrowing struct <c>E</c>:
    /// <c>{ E e = o.GetEnumerator(); while (e.MoveNext()) { T x = e.Current; body } }</c>,
    /// with <c>e</c> held as R27.41/R27.49 hold such a local, and named in contracts by
    /// <c>Pal.Enumerator&lt;E&gt;(x)</c>. <c>null</c> when <c>o</c> is no such object.
    /// </summary>
    // R27.51. The enumerator structs of the `foreach` statements over owners being lowered.
    private readonly List<BorrowContext> _heldForEach = [];

    private IrStmt? ForEachOwner(ForEachStatementSyntax node, IrLoc loc)
    {
        var self = model.GetEnclosingSymbol(node.SpanStart) as IMethodSymbol;
        var expr = ExprLowerer.Unparenthesized(node.Expression);
        INamedTypeSymbol? cls = expr is ThisExpressionSyntax ? self?.ContainingType
            : model.GetSymbolInfo(expr).Symbol switch
            {
                IParameterSymbol p => FrontendPass.ExactParameter(p, model.Compilation, known) ?? p.Type as INamedTypeSymbol,
                ILocalSymbol l => l.Type as INamedTypeSymbol,
                _ => null,
            };
        if (cls is not { TypeKind: TypeKind.Class } || !known.HasModel(cls)) return null;
        var getter = cls.GetMembers("GetEnumerator").OfType<IMethodSymbol>().FirstOrDefault(m =>
            m is { IsStatic: false, Parameters.IsEmpty: true, DeclaredAccessibility: Accessibility.Public } &&
            m.ReturnType is INamedTypeSymbol { TypeKind: TypeKind.Struct } r && Borrowing.IsBorrowing(r, known));
        if (getter?.ReturnType is not INamedTypeSymbol st) return null;
        var moveNext = st.GetMembers("MoveNext").OfType<IMethodSymbol>()
            .FirstOrDefault(m => m is { IsStatic: false, Parameters.IsEmpty: true });
        var current = st.GetMembers("Current").OfType<IPropertySymbol>()
            .FirstOrDefault(q => q is { IsStatic: false, GetMethod: not null });
        var owner = Borrowing.OwnerField(st, known)!;
        var variable = model.GetDeclaredSymbol(node) as ILocalSymbol;
        var receiver = _code.Lower(expr);
        if (moveNext is null || current?.GetMethod is null || variable is null ||
            known.MapType(st) is not { } structType || known.MapType(owner.Type) is not IrClassType ownerType ||
            known.MapType(variable.Type) is not { } elementType ||
            self is null || self.IsStatic || self.MethodKind == MethodKind.LambdaMethod ||
            !SymbolEqualityComparer.Default.Equals(self.ContainingType?.OriginalDefinition, owner.Type.OriginalDefinition) ||
            receiver is not IrVar { Name: var ownerName } ||
            (ownerName != Pal.Compiler.Emit.Names.This && !self.Parameters.Any(q => q.Name == ownerName)) ||
            node.Parent is not BlockSyntax ||
            node.Ancestors().TakeWhile(a => a is not (BaseMethodDeclarationSyntax or AccessorDeclarationSyntax))
                .Any(a => a is WhileStatementSyntax or DoStatementSyntax or ForStatementSyntax or
                          CommonForEachStatementSyntax or AnonymousFunctionExpressionSyntax or
                          LocalFunctionStatementSyntax or TryStatementSyntax or SwitchSectionSyntax))
        {
            diagnostics.Error("PALCS0714", Locations.From(node.Expression),
                $"`foreach` over `{node.Expression}`. A `foreach` over an object is translated in an " +
                "instance method of its class, over `this` or a parameter of the class, directly in a " +
                "block outside any loop, lambda or `try`, when the class's `GetEnumerator()` returns a " +
                "borrowing struct with `MoveNext()` and `Current` (doc/translation.md R27.51).");
            return new IrBlock(loc, []);
        }

        var vloc = Locations.From(node.Identifier);
        var name = ExprLowerer.ForEachEnumerator(variable.Name);
        var owned = Borrowing.OwnedFields(st, known);
        var held = new BorrowContext(st, owner, structType, ownerType, false, null)
        {
            Owned = owned,
            SelfName = name,
            OwnerName = ownerName,
            OwnedNames = owned.ToImmutableDictionary(f => f.Name, f => $"__pal_own_{name}{f.Name}"),
        };
        var ownedLocals = ImmutableArray.CreateBuilder<(string, string, IrClassType)>();
        foreach (var f in owned)
            if (known.MapType(f.Type) is IrClassType ot) ownedLocals.Add((f.Name, held.OwnedLocal(f), ot));
        var decl = new IrLocalDecl(vloc, name, structType, _code.OwnerCall(getter, receiver, vloc))
        {
            Owned = ownedLocals.ToImmutable(),
            HeldOwner = ownerName == Pal.Compiler.Emit.Names.This ? null : ownerName,
        };
        _code.HoldForEach(variable, held);
        _spec.HoldForEach(variable, held);
        _heldForEach.Add(held);
        var (invariants, decreases, body) = ExtractLoopSpecs(node.Statement);
        var first = new IrLocalDecl(vloc, variable.Name, elementType,
            _code.ToDeclared(_code.HeldCallOf(held, current.GetMethod, vloc), elementType)) { Immutable = true };
        var loop = new IrWhile(loc, _code.HeldCallOf(held, moveNext, vloc), invariants, decreases,
            new IrBlock(body.Loc, [first, .. ((IrBlock)body).Statements]));
        _heldForEach.Remove(held);
        return new IrBlock(loc, [decl, loop]) { Splice = true };
    }

    /// <summary>
    /// Pulls the leading <c>Pal.Invariant</c> / <c>Pal.Decreases</c> calls off a loop
    /// body (surface rule B1). They must lead: a loop specification describes the loop,
    /// so anything before it in the body would already have run under no specification.
    /// </summary>
    private (ImmutableArray<IrExpr> Invariants, IrExpr? Decreases, IrStmt Body) ExtractLoopSpecs(
        StatementSyntax bodySyntax, bool loop = true)
    {
        var invariants = ImmutableArray.CreateBuilder<IrExpr>();
        if (loop && borrow is { Constructor: false })
            invariants.AddRange(BorrowFacts.Invariants(borrow, known, Locations.From(bodySyntax)));
        // R27.41. So does a loop of a method that holds one, for each it holds.
        if (loop)
            foreach (var held in _spec.Held.Concat(_heldForEach))
                invariants.AddRange(BorrowFacts.Invariants(held, known, Locations.From(bodySyntax), snapshots: false));
        IrExpr? decreases = null;

        var statements = bodySyntax is BlockSyntax block
            ? block.Statements.ToList()
            : [bodySyntax];

        var leading = 0;
        while (leading < statements.Count)
        {
            if (statements[leading] is not ExpressionStatementSyntax
                { Expression: InvocationExpressionSyntax call }) break;
            if (model.GetSymbolInfo(call).Symbol is not IMethodSymbol m || !known.IsPalIntrinsic(m)) break;

            if (m.Name == nameof(PalLang.Pal.Invariant))
                invariants.Add(_spec.Lower(call.ArgumentList.Arguments[0].Expression));
            else if (m.Name == nameof(PalLang.Pal.Decreases))
                decreases = _spec.Lower(call.ArgumentList.Arguments[0].Expression);
            else break;

            leading++;
        }

        var rest = statements.Skip(leading).Select(Lower)
            .SelectMany(s => s is IrBlock { Splice: true } b ? b.Statements : [s]).ToImmutableArray();
        return (invariants.ToImmutable(), decreases,
            new IrBlock(Locations.From(bodySyntax), rest));
    }

    /// <summary>Lowers an expression in specification position.</summary>
    public IrExpr LowerSpec(ExpressionSyntax expression) => _spec.Lower(expression);

    /// <summary>
    /// An expression body <c>=&gt; e</c> of a member returning a value is <c>return e;</c>,
    /// and of one returning nothing is <c>e;</c>; each is lowered as that statement is.
    /// </summary>
    public IrStmt LowerArrow(ArrowExpressionClauseSyntax arrow)
    {
        var loc = Locations.From(arrow);
        if (model.GetEnclosingSymbol(arrow.Expression.SpanStart) is IMethodSymbol { ReturnsVoid: false } m)
            return new IrReturn(loc, _code.ToDeclared(_code.Lower(arrow.Expression), known.MapType(m.ReturnType)));
        if (arrow.Expression is ThrowExpressionSyntax th)
            return new IrThrow(loc, _code.Lower(th.Expression));
        return LowerSideEffect(arrow.Expression, loc);
    }

    private ITypeSymbol? ReturnType(ReturnStatementSyntax r) =>
        model.GetEnclosingSymbol(r.SpanStart) switch
        {
            IMethodSymbol { MethodKind: MethodKind.LambdaMethod or MethodKind.LocalFunction } => null,
            IMethodSymbol m => m.ReturnType,
            _ => null,
        };

    /// <summary>
    /// R23.2. <c>ArgumentOutOfRangeException.ThrowIfNegative(v)</c> and its siblings, at an
    /// integer type, are <c>if (v &lt; 0) throw new ArgumentOutOfRangeException();</c> and so
    /// on; <c>ArgumentNullException.ThrowIfNull(x)</c> at a non-nullable array or class type
    /// is nothing, since such a reference is not null (R10). The parameter-name argument
    /// the compiler supplies is a constant and is not evaluated. Null for any other call.
    /// </summary>
    private IrStmt? ArgumentGuard(IMethodSymbol method, SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc) =>
        IntegerGuard(method, args, loc) ?? OpaqueNullGuard(method, args, loc);

    private IrStmt? IntegerGuard(IMethodSymbol method, SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc)
    {
        var owner = method.ContainingType?.ToDisplayString();
        if (owner == "System.ArgumentNullException" && method.Name == "ThrowIfNull" && args.Count >= 1 &&
            args.Skip(1).All(a => model.GetConstantValue(a.Expression).HasValue) &&
            // R27.40. So is one at a non-nullable delegate type (R26.1).
            model.GetTypeInfo(args[0].Expression) is { Type: { } ntType } nt &&
            (ntType is IArrayTypeSymbol or { TypeKind: TypeKind.Class or TypeKind.Delegate } ||
             // R27.46. So is one at an `[Exactly]` parameter, which is an object of its class.
             model.GetSymbolInfo(args[0].Expression).Symbol is IParameterSymbol xp &&
             FrontendPass.ExactParameter(xp, model.Compilation, known) is not null) &&
            nt.Nullability.FlowState == NullableFlowState.NotNull &&
            nt.Type.NullableAnnotation != NullableAnnotation.Annotated)
            return new IrBlock(loc, []);

        // R33.1. System.Collections' own polyfills of the same guards (its `ThrowHelper`,
        // compiled where the BCL's are missing) are read as the BCL's.
        ITypeSymbol? ty = null;
        if (owner == "System.ArgumentOutOfRangeException" && method.IsGenericMethod &&
            method.TypeArguments is [var bclTy])
            ty = bclTy;
        else if (owner == "System.Collections.ThrowHelper" && method.IsStatic &&
                 method.Name is "ThrowIfNegative" or "ThrowIfLessThan" or "ThrowIfGreaterThan" &&
                 method.Parameters is [var first, ..])
            ty = method.IsGenericMethod ? method.TypeArguments[0] : first.Type;
        if (ty is null || !IsIntegral(ty.SpecialType))
            return null;
        (BinOp op, bool unary)? shape = method.Name switch
        {
            "ThrowIfNegative" => (BinOp.Lt, true),
            "ThrowIfNegativeOrZero" => (BinOp.Le, true),
            "ThrowIfZero" => (BinOp.Eq, true),
            "ThrowIfLessThan" => (BinOp.Lt, false),
            "ThrowIfLessThanOrEqual" => (BinOp.Le, false),
            "ThrowIfGreaterThan" => (BinOp.Gt, false),
            "ThrowIfGreaterThanOrEqual" => (BinOp.Ge, false),
            "ThrowIfEqual" => (BinOp.Eq, false),
            "ThrowIfNotEqual" => (BinOp.Ne, false),
            _ => null,
        };
        int operands = shape is { unary: true } ? 1 : 2;
        if (shape is not { } s || args.Count < operands ||
            args.Skip(operands).Any(a => !model.GetConstantValue(a.Expression).HasValue))
            return null;
        var type = known.MapType(ty);
        var left = _code.Lower(args[0].Expression);
        var right = s.unary ? new IrLiteral(loc, 0) { Type = type } : _code.Lower(args[1].Expression);
        return new IrIf(loc, new IrBinary(loc, s.op, left, right) { Type = IrPrim.Bool },
            new IrThrow(loc, _code.LibraryException(loc, "System.ArgumentOutOfRangeException")), null);

        static bool IsIntegral(SpecialType t) => t is SpecialType.System_Int32 or SpecialType.System_Int64
            or SpecialType.System_UInt32 or SpecialType.System_UInt64 or SpecialType.System_Int16
            or SpecialType.System_UInt16 or SpecialType.System_Byte or SpecialType.System_SByte;
    }

    /// <summary>
    /// R25.7. <c>ArgumentNullException.ThrowIfNull(x)</c> at a type parameter or a comparer,
    /// and <c>ArgumentOutOfRangeException.ThrowIfNegative(n)</c> at <c>int</c>: each is
    /// <c>if (test) throw new E(...)</c>, where the parameter name the BCL passes is not
    /// modelled (R21.7). Any other guard is an ordinary call and is refused as one.
    /// </summary>
    private IrStmt? OpaqueNullGuard(IMethodSymbol method, SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc)
    {
        if (!method.IsStatic || args.Count != 1 || args[0].NameColon is not null) return null;
        var owner = method.ContainingType?.ToDisplayString();
        IrExpr test;
        if (owner == "System.ArgumentNullException" && method.Name == "ThrowIfNull")
        {
            var value = ExprLowerer.Unboxed(_code.Lower(args[0].Expression));
            if (!Sorted.HasOpaqueNull(value.Type)) return null;
            test = Sorted.IsNull(loc, value);
        }
        else if (owner == "System.ArgumentOutOfRangeException" && method.Name == "ThrowIfNegative" &&
                 model.GetTypeInfo(args[0].Expression).Type?.SpecialType == SpecialType.System_Int32)
        {
            test = new IrBinary(loc, BinOp.Lt, _code.Lower(args[0].Expression),
                new IrLiteral(loc, 0) { Type = IrPrim.Int }) { Type = IrPrim.Bool };
        }
        else return null;
        return new IrIf(loc, test, new IrThrow(loc, _code.LibraryException(loc, owner)), null);
    }

    /// <summary>
    /// R22.20, R22.25. <c>Array.Copy</c> (3- and 5-argument), <c>Array.Clear(a, i, n)</c>
    /// and <c>Array.Reverse(a, i, n)</c>, or null when the call is not one of them.
    /// </summary>

    private IrStmt? ArrayBulkOp(IMethodSymbol method, SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc)
    {
        if (args.Count != method.Parameters.Length) return null;
        var byParam = new ExpressionSyntax[args.Count];
        for (int i = 0; i < args.Count; i++)
        {
            int at = args[i].NameColon is { } nc
                ? method.Parameters.IndexOf(method.Parameters.FirstOrDefault(p => p.Name == nc.Name.Identifier.ValueText)!)
                : i;
            if (at < 0 || byParam[at] is not null) return null;
            byParam[at] = args[i].Expression;
        }
        bool IsInt(int i) => method.Parameters[i].Type.SpecialType == SpecialType.System_Int32;
        IArrayTypeSymbol? ArrayOf(ExpressionSyntax e) =>
            model.GetTypeInfo(e).Type is IArrayTypeSymbol { Rank: 1 } at ? at : null;
        IrExpr L(int i) => _code.Lower(byParam[i]);

        switch (method.Name, args.Count)
        {
            case ("Copy", 3) when IsInt(2) &&
                ArrayOf(byParam[0]) is { } st && ArrayOf(byParam[1]) is { } dt &&
                SymbolEqualityComparer.Default.Equals(st.ElementType, dt.ElementType):
                return new IrArrayOp(loc, ArrayOpKind.Copy, [L(0), L(1), L(2)]);

            // A copy within one array may overlap, and is a `Move`; one array is
            // recognised syntactically, and two distinct expressions must then denote
            // distinct arrays, which the separate permissions the copy needs ensure.
            case ("Copy", 5) when IsInt(1) && IsInt(3) && IsInt(4) &&
                ArrayOf(byParam[0]) is { } st && ArrayOf(byParam[2]) is { } dt &&
                SymbolEqualityComparer.Default.Equals(st.ElementType, dt.ElementType):
                return SyntaxFactory.AreEquivalent(byParam[0], byParam[2])
                    ? new IrArrayOp(loc, ArrayOpKind.Move, [L(0), L(1), L(3), L(4)])
                    : new IrArrayOp(loc, ArrayOpKind.CopyAt, [L(0), L(1), L(2), L(3), L(4)]);

            case ("Clear", 3) when IsInt(1) && IsInt(2) && ArrayOf(byParam[0]) is { } ct:
                foreach (var tp in ExprLowerer.TypeParametersIn(ct.ElementType))
                    _code.DefaultedTypeParameters.Add(tp.Name);
                return new IrArrayOp(loc, ArrayOpKind.Clear, [L(0), L(1), L(2)]);

            // R24.10. `Array.Clear(a)` clears the whole array.
            case ("Clear", 1) when ArrayOf(byParam[0]) is { } wt:
            {
                foreach (var wtp in ExprLowerer.TypeParametersIn(wt.ElementType))
                    _code.DefaultedTypeParameters.Add(wtp.Name);
                var whole = L(0);
                return new IrArrayOp(loc, ArrayOpKind.Clear,
                    [whole, new IrLiteral(loc, 0) { Type = IrPrim.Int },
                     new IrLength(loc, L(0)) { Type = IrPrim.Int }]);
            }

            case ("Reverse", 3) when method.IsGenericMethod && IsInt(1) && IsInt(2) && ArrayOf(byParam[0]) is { }:
                return new IrArrayOp(loc, ArrayOpKind.Reverse, [L(0), L(1), L(2)]);

            // R26.7. `Array.Sort<T>(a, index, length, comparer)`.
            case ("Sort", 4) when method.IsGenericMethod && IsInt(1) && IsInt(2) && ArrayOf(byParam[0]) is { } &&
                known.MapType(method.Parameters[3].Type) is IrUserSpecType { FStar: Sorted.ComparerType }:
                return new IrArrayOp(loc, ArrayOpKind.Sort, [L(0), L(1), L(2), L(3)]);
        }
        return null;
    }
}
