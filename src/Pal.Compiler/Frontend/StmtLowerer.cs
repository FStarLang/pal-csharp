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
            ReturnStatementSyntax r => new IrReturn(loc,
                r.Expression is null ? null : _code.Lower(r.Expression)),
            BreakStatementSyntax => new IrBreak(loc),
            ContinueStatementSyntax => new IrContinue(loc),
            EmptyStatementSyntax => new IrBlock(loc, []),
            _ => UnsupportedStatement(node, loc),
        };
    }

    private IrStmt UnsupportedStatement(SyntaxNode node, IrLoc loc)
    {
        diagnostics.Unsupported(loc, $"The statement `{node.Kind()}`");
        return new IrBlock(loc, []);
    }

    private IrBlock LowerBlock(BlockSyntax block) =>
        new(Locations.From(block), [.. block.Statements.Select(Lower)]);

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
                v.Initializer is null ? null : _code.Lower(v.Initializer.Value)));
        }

        return statements.Count == 1 ? statements[0] : new IrBlock(loc, statements.ToImmutable());
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
        var lowered = _code.Lower(target);
        return new IrAssign(loc, lowered, new IrBinary(loc, op, lowered, new IrLiteral(loc, 1)));
    }

    private IrStmt LowerAssignment(AssignmentExpressionSyntax node, IrLoc loc)
    {
        var target = _code.Lower(node.Left);
        var value = _code.Lower(node.Right);

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
            _ => throw new NotSupportedException(node.Kind().ToString()),
        };

        return new IrAssign(loc, target, op is null ? value : new IrBinary(loc, op.Value, target, value));
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
            { Kind = CalleeKind.Lemma };
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
