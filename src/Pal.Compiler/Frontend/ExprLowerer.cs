using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Lowers bound C# expressions to <see cref="IrExpr"/>.
///
/// <para>
/// The lowering is <em>structure preserving</em> (doc/translation.md §0 rule 2): it
/// neither folds constants, nor reassociates, nor recognises idioms. Every node here
/// maps one C# construct to one IR construct.
/// </para>
/// </summary>
public sealed class ExprLowerer(SemanticModel model, WellKnown known, DiagnosticBag diagnostics, bool specPosition)
{
    /// <summary>
    /// True when lowering a specification. In spec position arithmetic is mathematical
    /// (doc/translation.md §6), so no overflow obligations are raised.
    /// </summary>
    public bool SpecPosition { get; } = specPosition;

    public IrExpr Lower(ExpressionSyntax node)
    {
        var loc = Locations.From(node);
        var type = known.MapType(model.GetTypeInfo(node).Type);

        IrExpr result = node switch
        {
            ParenthesizedExpressionSyntax p => Lower(p.Expression),
            // `default` and `default(T)` are the same expression; both must be matched
            // before the general literal case, which would otherwise see a token with
            // no value and produce a nonsense constant.
            DefaultExpressionSyntax => Default(node, loc),
            LiteralExpressionSyntax l when l.IsKind(SyntaxKind.DefaultLiteralExpression) =>
                Default(node, loc),
            LiteralExpressionSyntax l => LowerLiteral(l, loc),
            IdentifierNameSyntax id => LowerIdentifier(id, loc),
            MemberAccessExpressionSyntax m => LowerMemberAccess(m, loc),
            ElementAccessExpressionSyntax e => LowerElementAccess(e, loc),
            BinaryExpressionSyntax b => LowerBinary(b, loc),
            PrefixUnaryExpressionSyntax u => LowerPrefixUnary(u, loc),
            ConditionalExpressionSyntax c =>
                new IrConditional(loc, Lower(c.Condition), Lower(c.WhenTrue), Lower(c.WhenFalse)),
            CastExpressionSyntax c when known.MapType(model.GetTypeInfo(c.Type).Type) is { } t =>
                new IrConvert(loc, t, Lower(c.Expression)),
            InvocationExpressionSyntax i => LowerInvocation(i, loc),
            ObjectCreationExpressionSyntax o => LowerObjectCreation(o, loc),
            ImplicitObjectCreationExpressionSyntax o => LowerObjectCreation(o, loc),
            _ => Unsupported(node, loc),
        };

        return type is null ? result : result with { Type = type };
    }

    /// <summary>
    /// R3.5. <c>new S { f = e, … }</c>. Only object-initializer syntax is translated:
    /// a user-written constructor has a body, and running that body at every
    /// construction site is method translation, not expression translation.
    /// </summary>
    private IrExpr LowerObjectCreation(BaseObjectCreationExpressionSyntax node, IrLoc loc)
    {
        if (model.GetTypeInfo(node).Type is not INamedTypeSymbol { TypeKind: TypeKind.Struct } named)
            return Unsupported(node, loc);

        if (node.ArgumentList is { Arguments.Count: > 0 })
        {
            diagnostics.Unsupported(loc, $"A constructor call on `{named.Name}`",
                "Use object-initializer syntax: `new " + named.Name + " { Field = value, … }`.");
            return new IrLiteral(loc, null);
        }

        var given = new List<IrFieldInit>();
        foreach (var expr in node.Initializer?.Expressions ?? default)
        {
            if (expr is not AssignmentExpressionSyntax { Left: IdentifierNameSyntax name } assign)
            {
                diagnostics.Unsupported(Locations.From(expr), $"The initializer `{Trim(expr)}`");
                continue;
            }
            given.Add(new IrFieldInit(name.Identifier.ValueText, Lower(assign.Right)));
        }

        return Construct(loc, named.Name, named, given);
    }

    /// <summary>
    /// R3.5. Builds the complete field list: C# guarantees a value type is fully
    /// initialized, so a field the source did not mention takes its type's zero.
    /// </summary>
    private IrExpr Construct(
        IrLoc loc, string name, INamedTypeSymbol? symbol,
        IReadOnlyList<IrFieldInit> given)
    {
        if (symbol is null)
        {
            diagnostics.Unsupported(loc, $"A value of type `{name}`");
            return new IrLiteral(loc, null);
        }

        var fields = ImmutableArray.CreateBuilder<IrFieldInit>();
        foreach (var (field, type) in StructFields(symbol))
        {
            var supplied = given.FirstOrDefault(g => g.Field == field);
            if (supplied is not null) { fields.Add(supplied); continue; }
            if (Zero(loc, type) is not { } zero)
            {
                diagnostics.Unsupported(loc, $"The default value of `{name}.{field}`");
                return new IrLiteral(loc, null);
            }
            fields.Add(new IrFieldInit(field, zero));
        }

        foreach (var g in given)
            if (!fields.Any(f => f.Field == g.Field))
                diagnostics.Unsupported(loc, $"The initializer for `{name}.{g.Field}`");

        return new IrNew(loc, name, fields.ToImmutable());
    }

    /// <summary>The fields of a struct, in declaration order; see R3.4.</summary>
    private static IEnumerable<(string Name, ITypeSymbol Type)> StructFields(INamedTypeSymbol symbol)
    {
        foreach (var member in symbol.GetMembers())
        {
            switch (member)
            {
                case IFieldSymbol { IsStatic: false, IsConst: false, AssociatedSymbol: null } f:
                    yield return (f.Name, f.Type); break;
                case IPropertySymbol { IsStatic: false, IsIndexer: false } p
                    when symbol.GetMembers().OfType<IFieldSymbol>().Any(
                        f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, p)):
                    yield return (p.Name, p.Type); break;
            }
        }
    }

    private IrExpr? Zero(IrLoc loc, ITypeSymbol type)
    {
        var mapped = known.MapType(type);
        return mapped switch
        {
            IrPrim { Kind: PrimKind.Bool } => new IrLiteral(loc, false) { Type = mapped },
            IrPrim p when p.IsMachineInt || p.Kind is PrimKind.SpecInt or PrimKind.SpecNat =>
                new IrLiteral(loc, 0) { Type = mapped },
            IrNamedType n when type is INamedTypeSymbol named =>
                Construct(loc, n.Name, named, []) is IrNew nested ? nested with { Type = mapped } : null,
            _ => null,
        };
    }

    private IrExpr Unsupported(ExpressionSyntax node, IrLoc loc)
    {
        diagnostics.Unsupported(loc, $"The expression `{Trim(node)}`");
        return new IrLiteral(loc, null);
    }

    private static string Trim(SyntaxNode node)
    {
        var text = node.ToString();
        return text.Length <= 60 ? text : text[..57] + "...";
    }

    private static IrExpr LowerLiteral(LiteralExpressionSyntax node, IrLoc loc) =>
        new IrLiteral(loc, node.Token.Value);

    /// <summary>R3.5. <c>default</c> at any translatable type.</summary>
    private IrExpr Default(ExpressionSyntax node, IrLoc loc)
    {
        if (model.GetTypeInfo(node).Type is not { } type) return Unsupported(node, loc);
        if (Zero(loc, type) is { } zero) return zero;
        diagnostics.Unsupported(loc, $"`default` at type `{type}`");
        return new IrLiteral(loc, null);
    }

    private IrExpr LowerIdentifier(IdentifierNameSyntax node, IrLoc loc)
    {
        var symbol = model.GetSymbolInfo(node).Symbol;

        // A postcondition's `Result` is a parameter of the generated shim, not a name in
        // the user's program; it denotes the value the method returns.
        if (symbol is IParameterSymbol { Name: SpecBinder.ResultParameter } p &&
            p.ContainingSymbol.Name.StartsWith(SpecBinder.ShimMethodPrefix, StringComparison.Ordinal))
            return new IrResult(loc);

        return symbol switch
        {
            IParameterSymbol or ILocalSymbol or IRangeVariableSymbol => new IrVar(loc, node.Identifier.ValueText),
            IFieldSymbol f when f.HasConstantValue => new IrLiteral(loc, f.ConstantValue),
            _ => Unsupported(node, loc),
        };
    }

    private IrExpr LowerMemberAccess(MemberAccessExpressionSyntax node, IrLoc loc)
    {
        var symbol = model.GetSymbolInfo(node).Symbol;
        var receiverType = model.GetTypeInfo(node.Expression).Type;

        // `a.Length` on a real array is a pure function of the array (doc §3, R3.3).
        if (node.Name.Identifier.ValueText == "Length" && receiverType is IArrayTypeSymbol)
            return new IrLength(loc, Lower(node.Expression));

        // `s.Length` on a ghost sequence is `Seq.length`.
        if (node.Name.Identifier.ValueText == "Length" && known.IsSeq(receiverType))
            return new IrSeqOp(loc, SeqOpKind.Length, [Lower(node.Expression)]);

        if (symbol is IFieldSymbol { HasConstantValue: true } konst)
            return new IrLiteral(loc, konst.ConstantValue);

        if (symbol is IFieldSymbol or IPropertySymbol && receiverType?.TypeKind == TypeKind.Struct)
            return new IrField(loc, Lower(node.Expression), node.Name.Identifier.ValueText);

        return Unsupported(node, loc);
    }

    private IrExpr LowerElementAccess(ElementAccessExpressionSyntax node, IrLoc loc)
    {
        if (node.ArgumentList.Arguments.Count != 1)
        {
            diagnostics.Unsupported(loc, "Multi-dimensional indexing");
            return new IrLiteral(loc, null);
        }

        var receiver = Lower(node.Expression);
        var index = Lower(node.ArgumentList.Arguments[0].Expression);
        var receiverType = model.GetTypeInfo(node.Expression).Type;

        return known.IsSeq(receiverType)
            ? new IrSeqOp(loc, SeqOpKind.Index, [receiver, index])
            : new IrElement(loc, receiver, index);
    }

    private IrExpr LowerBinary(BinaryExpressionSyntax node, IrLoc loc)
    {
        var op = node.Kind() switch
        {
            SyntaxKind.AddExpression => BinOp.Add,
            SyntaxKind.SubtractExpression => BinOp.Sub,
            SyntaxKind.MultiplyExpression => BinOp.Mul,
            SyntaxKind.DivideExpression => BinOp.Div,
            SyntaxKind.ModuloExpression => BinOp.Rem,
            SyntaxKind.LogicalAndExpression => BinOp.And,
            SyntaxKind.LogicalOrExpression => BinOp.Or,
            SyntaxKind.BitwiseAndExpression => BinOp.BitAnd,
            SyntaxKind.BitwiseOrExpression => BinOp.BitOr,
            SyntaxKind.ExclusiveOrExpression => BinOp.BitXor,
            SyntaxKind.LeftShiftExpression => BinOp.Shl,
            SyntaxKind.RightShiftExpression => BinOp.Shr,
            SyntaxKind.EqualsExpression => BinOp.Eq,
            SyntaxKind.NotEqualsExpression => BinOp.Ne,
            SyntaxKind.LessThanExpression => BinOp.Lt,
            SyntaxKind.LessThanOrEqualExpression => BinOp.Le,
            SyntaxKind.GreaterThanExpression => BinOp.Gt,
            SyntaxKind.GreaterThanOrEqualExpression => BinOp.Ge,
            _ => (BinOp?)null,
        };

        if (op is null) return Unsupported(node, loc);
        return new IrBinary(loc, op.Value, Lower(node.Left), Lower(node.Right));
    }

    private IrExpr LowerPrefixUnary(PrefixUnaryExpressionSyntax node, IrLoc loc)
    {
        var op = node.Kind() switch
        {
            SyntaxKind.UnaryMinusExpression => UnOp.Neg,
            SyntaxKind.LogicalNotExpression => UnOp.Not,
            SyntaxKind.BitwiseNotExpression => UnOp.BitNot,
            SyntaxKind.UnaryPlusExpression => (UnOp?)null,
            _ => null,
        };

        if (node.IsKind(SyntaxKind.UnaryPlusExpression)) return Lower(node.Operand);
        if (op is null) return Unsupported(node, loc);
        return new IrUnary(loc, op.Value, Lower(node.Operand));
    }

    private IrExpr LowerInvocation(InvocationExpressionSyntax node, IrLoc loc)
    {
        if (model.GetSymbolInfo(node).Symbol is not IMethodSymbol method) return Unsupported(node, loc);

        var args = node.ArgumentList.Arguments;

        if (known.IsPalIntrinsic(method))
            return LowerIntrinsic(method, node, args, loc);

        var kind = Declarations.KindOf(method, known);
        if (kind is null)
        {
            diagnostics.Unsupported(loc,
                $"A call to `{method.Name}`",
                "Only pal-csharp methods, [Spec] functions and [Lemma]s can be called.");
            return new IrLiteral(loc, null);
        }

        return new IrCall(loc, Naming.Of(method), [.. args.Select(a => Lower(a.Expression))]) { Kind = kind.Value };
    }

    private IrExpr LowerIntrinsic(
        IMethodSymbol method, InvocationExpressionSyntax node,
        SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc)
    {
        IrExpr Arg(int i) => Lower(args[i].Expression);

        switch (method.Name)
        {
            case nameof(PalLang.Pal.Old): return new IrOld(loc, Arg(0));
            case nameof(PalLang.Pal.Result): return new IrResult(loc);
            case nameof(PalLang.Pal.Live): return new IrLive(loc, Arg(0));
            case nameof(PalLang.Pal.Implies): return new IrBinary(loc, BinOp.Implies, Arg(0), Arg(1));
            case nameof(PalLang.Pal.Iff): return new IrBinary(loc, BinOp.Iff, Arg(0), Arg(1));
            case nameof(PalLang.Pal.Contents): return new IrContents(loc, Arg(0));
            case nameof(PalLang.Pal.IsPermutation):
                return new IrSeqOp(loc, SeqOpKind.IsPermutation, [Arg(0), Arg(1)]);
            case nameof(PalLang.Pal.SetAt):
                return new IrSeqOp(loc, SeqOpKind.SetAt, [Arg(0), Arg(1), Arg(2)]);
            case nameof(PalLang.Pal.Slice):
                return new IrSeqOp(loc, SeqOpKind.Slice, [Arg(0), Arg(1), Arg(2)]);
            case nameof(PalLang.Pal.Forall) or nameof(PalLang.Pal.Exists):
                return LowerQuantifier(method.Name == nameof(PalLang.Pal.Forall), args, loc);
            case nameof(PalLang.Pal.InlinePulse) when ConstantString(args[0].Expression) is { } text:
                return new IrInlinePulse(loc, text);
            default:
                diagnostics.Unsupported(loc, $"`Pal.{method.Name}` in this position");
                return new IrLiteral(loc, null);
        }
    }

    private IrExpr LowerQuantifier(
        bool isForall, SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc)
    {
        if (args.Count != 1 || args[0].Expression is not ParenthesizedLambdaExpressionSyntax lambda)
        {
            diagnostics.Unsupported(loc, "A quantifier whose body is not a lambda",
                "Write `Pal.Forall((int i) => ...)`.");
            return new IrLiteral(loc, null);
        }

        var binders = ImmutableArray.CreateBuilder<IrBinder>();
        foreach (var p in lambda.ParameterList.Parameters)
        {
            var symbol = model.GetDeclaredSymbol(p);
            var type = known.MapType(symbol?.Type);
            if (type is null)
            {
                diagnostics.Unsupported(Locations.From(p), $"The quantifier binder type `{p.Type}`");
                type = IrPrim.SpecIntType;
            }
            binders.Add(new IrBinder(p.Identifier.ValueText, type));
        }

        if (lambda.ExpressionBody is null)
        {
            diagnostics.Unsupported(loc, "A quantifier with a statement body",
                "The body must be a single expression.");
            return new IrLiteral(loc, null);
        }

        return new IrQuantifier(loc, isForall, binders.ToImmutable(), Lower(lambda.ExpressionBody));
    }

    public string? ConstantString(ExpressionSyntax expression) =>
        model.GetConstantValue(expression) is { HasValue: true, Value: string s } ? s : null;
}
