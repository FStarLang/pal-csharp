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
    ImmutableHashSet<string>? objectFields = null)
{
    private readonly ExprLowerer _code =
        new(model, known, diagnostics, specPosition: false) { ObjectFields = objectFields ?? [] };
    private readonly ExprLowerer _spec =
        new(model, known, diagnostics, specPosition: true) { ObjectFields = objectFields ?? [] };

    /// <summary>
    /// R4.12c. A constructor initializer is an expression that is not inside any statement,
    /// so the one caller that needs it reaches the expression lowerer directly.
    /// </summary>
    public ExprLowerer Expressions => _code;

    public IrStmt Lower(StatementSyntax node)
    {
        var loc = Locations.From(node);
        return node switch
        {
            BlockSyntax b => LowerBlock(b),
            LocalDeclarationStatementSyntax d => LowerLocalDeclaration(d, loc),
            ExpressionStatementSyntax e => LowerExpressionStatement(e, loc),
            IfStatementSyntax i => new IrIf(loc, _code.Lower(i.Condition),
                Lower(i.Statement), i.Else is null ? null : Lower(i.Else.Statement)),
            WhileStatementSyntax w => LowerWhile(w, loc),
            ForStatementSyntax f => LowerFor(f, loc),
            ForEachStatementSyntax f => LowerForEach(f, loc),
            ReturnStatementSyntax r => new IrReturn(loc,
                r.Expression is null ? null : _code.Lower(r.Expression)),
            BreakStatementSyntax => new IrBreak(loc),
            ContinueStatementSyntax => new IrContinue(loc),
            SwitchStatementSyntax s => LowerSwitch(s, loc),
            GotoStatementSyntax g => LowerGoto(g, loc),
            EmptyStatementSyntax => new IrBlock(loc, []),
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
        var (invariants, decreases, body) = ExtractLoopSpecs(node.Block);
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
        if (jump is null) return UnsupportedStatement(node, loc);

        diagnostics.Unsupported(loc, $"A {jump} statement",
            "It re-introduces the fallthrough C# otherwise forbids, and an if/else chain " +
            "(R5.14) has no way to enter one arm from another. Where the target section " +
            "is to run *instead*, write its labels on this section as well; where it is " +
            "to run *as well*, lift the shared work into a method both sections call.");
        return new IrBlock(loc, []);
    }

    private IrBlock LowerBlock(BlockSyntax block) =>
        new(Locations.From(block), [.. block.Statements.Select(Lower)]);

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
            statements.Add(new IrLocalDecl(Locations.From(v), v.Identifier.ValueText, type,
                v.Initializer is null ? null : _code.Lower(v.Initializer.Value))
            {
                Immutable = v.Initializer is not null && symbol is not null &&
                            type is IrPrim { Kind: PrimKind.Bool or PrimKind.String } or IrOptionType
                                or IrUserSpecType or IrExnType &&
                            NeverWritten(symbol, node.Parent ?? node),
            });
        }

        return statements.Count == 1 ? statements[0] : new IrBlock(loc, statements.ToImmutable());
    }

    /// <summary>
    /// R5.2a. Whether nothing in <paramref name="scope"/> writes <paramref name="local"/>
    /// after its declaration: no assignment, compound assignment, increment or decrement has
    /// it as its target, and it is never passed by <c>ref</c> or <c>out</c>. Such a local
    /// names one value for its whole life, and is bound as one rather than kept in a cell.
    /// An arithmetic local keeps its cell: its value then reaches the solver as a name
    /// rather than as its initialiser inlined, which arithmetic proofs depend on.
    /// </summary>
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
                RefExpressionSyntax r => r.Expression,
                _ => null,
            };
            while (target is ParenthesizedExpressionSyntax or MemberAccessExpressionSyntax or ElementAccessExpressionSyntax)
                target = target switch
                {
                    ParenthesizedExpressionSyntax p => p.Expression,
                    MemberAccessExpressionSyntax m => m.Expression,
                    ElementAccessExpressionSyntax e => e.Expression,
                    _ => target,
                };
            if (target is IdentifierNameSyntax id &&
                SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(id).Symbol, local))
                return false;
        }
        return true;
    }

    private IrStmt LowerExpressionStatement(ExpressionStatementSyntax node, IrLoc loc) =>
        LowerSideEffect(node.Expression, loc);

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
                return LowerCallStatement(call, loc);

            default:
                return UnsupportedStatement(expression, loc);
        }
    }

    private IrStmt Step(ExpressionSyntax target, BinOp op, IrLoc loc)
    {
        // R5.3 expands `x++` into `x = x + 1`, which names the L-value twice. C# evaluates
        // it once, so anything effectful in it is hoisted first and both copies share it.
        var lowered = _code.LinearizeLValue(_code.Lower(target), out var prelude);
        var assign = new IrAssign(loc, lowered, new IrBinary(loc, op, lowered, new IrLiteral(loc, 1)));
        return prelude.IsEmpty ? assign : new IrBlock(loc, [.. prelude, assign]);
    }

    private IrStmt LowerAssignment(AssignmentExpressionSyntax node, IrLoc loc)
    {
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

        if (op is null && !node.IsKind(SyntaxKind.SimpleAssignmentExpression))
        {
            diagnostics.Unsupported(loc, $"The assignment operator `{node.OperatorToken}`");
            return new IrBlock(loc, []);
        }

        var target = _code.Lower(node.Left);
        var value = _code.Lower(node.Right);

        if (op is null) return new IrAssign(loc, target, value);

        var linear = _code.LinearizeLValue(target, out var prelude);
        var assign = new IrAssign(loc, linear, new IrBinary(loc, op.Value, linear, value));
        return prelude.IsEmpty ? assign : new IrBlock(loc, [.. prelude, assign]);
    }

    /// <summary>
    /// A call in statement position is either a proof-annotation intrinsic, a
    /// <c>[Lemma]</c> application, or an ordinary method call.
    /// </summary>
    private IrStmt LowerCallStatement(InvocationExpressionSyntax node, IrLoc loc)
    {
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

    private IrStmt LowerWhile(WhileStatementSyntax node, IrLoc loc)
    {
        var (invariants, decreases, body) = ExtractLoopSpecs(node.Statement);
        return new IrWhile(loc, _code.Lower(node.Condition), invariants, decreases, body);
    }

    private IrStmt LowerFor(ForStatementSyntax node, IrLoc loc)
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
                    v.Initializer is null ? null : _code.Lower(v.Initializer.Value)));
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
    private IrStmt LowerForEach(ForEachStatementSyntax node, IrLoc loc)
    {
        var collectionType = model.GetTypeInfo(node.Expression).Type;
        var symbol = model.GetSymbolInfo(node.Expression).Symbol;
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
    /// Pulls the leading <c>Pal.Invariant</c> / <c>Pal.Decreases</c> calls off a loop
    /// body (surface rule B1). They must lead: a loop specification describes the loop,
    /// so anything before it in the body would already have run under no specification.
    /// </summary>
    private (ImmutableArray<IrExpr> Invariants, IrExpr? Decreases, IrStmt Body) ExtractLoopSpecs(
        StatementSyntax bodySyntax)
    {
        var invariants = ImmutableArray.CreateBuilder<IrExpr>();
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

        var rest = statements.Skip(leading).Select(Lower).ToImmutableArray();
        return (invariants.ToImmutable(), decreases,
            new IrBlock(Locations.From(bodySyntax), rest));
    }

    /// <summary>Lowers an expression in specification position.</summary>
    public IrExpr LowerSpec(ExpressionSyntax expression) => _spec.Lower(expression);
}
