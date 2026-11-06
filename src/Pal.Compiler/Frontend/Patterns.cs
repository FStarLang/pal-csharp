using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// §21. Closed hierarchies of records and the pattern matching over them (R21.3–R21.7).
///
/// <para>A pattern lowers to a boolean condition over a <em>pure</em> subject, together
/// with bindings: each variable a pattern declares denotes a pure expression over the
/// subject — the subject itself, or a projection of one of its components — and every
/// later mention of the variable is that expression. Nothing is copied; a record is a
/// value, so naming a component twice reads the same thing twice.</para>
/// </summary>
public sealed partial class ExprLowerer
{
    private readonly Dictionary<ISymbol, IrExpr> _patternBindings = new(SymbolEqualityComparer.Default);

    private static readonly IrPrim Bool = new(PrimKind.Bool);

    private static IrExpr True(IrLoc loc) => new IrLiteral(loc, true) { Type = Bool };

    private static bool IsTrue(IrExpr e) => e is IrLiteral { Value: true };

    private static IrExpr False(IrLoc loc) => new IrLiteral(loc, false) { Type = Bool };

    private static bool IsFalse(IrExpr e) => e is IrLiteral { Value: false };

    /// <summary>R27.1. A translated class all of whose translated objects are of it exactly.</summary>
    private INamedTypeSymbol? ExactClassType(ITypeSymbol? type) =>
        type is INamedTypeSymbol { TypeKind: TypeKind.Class, IsAbstract: false } c && known.HasModel(c) &&
        (c.IsSealed || FrontendPass.EffectivelySealed(c.OriginalDefinition, known))
            ? c : null;

    /// <summary>
    /// R27.46. <c>e is D</c> with a type on the right. It is the type pattern <c>e is D</c>
    /// written without the pattern syntax.
    /// </summary>
    private IrExpr LowerIsType(BinaryExpressionSyntax node, IrLoc loc)
    {
        if (model.GetTypeInfo(node.Right).Type is not { } target) return Unsupported(node, loc);
        var prelude = ImmutableArray.CreateBuilder<IrStmt>();
        var subject = PatternSubject(node.Left, prelude);
        var cond = TypeTest(node, target, subject, out _);
        return WithPrelude(loc, prelude, cond with { Type = Bool });
    }

    private static IrExpr Conj(IrLoc loc, IrExpr a, IrExpr b) =>
        IsTrue(a) ? b : IsTrue(b) ? a : new IrBinary(loc, BinOp.And, a, b) { Type = Bool };

    /// <summary>A pattern's subject: one value, or the components of a tuple literal.</summary>
    private sealed record Subject(IrExpr? Value, ITypeSymbol? Type, ImmutableArray<Subject> Components)
    {
        public static Subject Of(IrExpr value, ITypeSymbol? type) => new(value, type, default);
    }

    /// <summary>
    /// R21.3. The subject is evaluated once. A parameter, a literal or an expression with
    /// no effect is already a value and is used as it stands; anything else is bound to a
    /// fresh immutable local first.
    /// </summary>
    private Subject PatternSubject(ExpressionSyntax node, ImmutableArray<IrStmt>.Builder prelude)
    {
        if (node is TupleExpressionSyntax tuple)
            return new Subject(null, null,
                [.. tuple.Arguments.Select(a => PatternSubject(a.Expression, prelude))]);

        var value = Lower(node);
        var type = model.GetTypeInfo(node).Type;
        // R27.46. An `[Exactly]` parameter is an object of its class.
        if (model.GetSymbolInfo(node).Symbol is IParameterSymbol ep &&
            FrontendPass.ExactParameter(ep, model.Compilation, known) is { } exact)
            type = exact;
        if (SpecPosition || !HasEffect(value)) return Subject.Of(value, type);

        var loc = value.Loc;
        var name = Fresh("subject");
        prelude.Add(new IrLocalDecl(loc, name, value.Type!, value) { Immutable = true });
        return Subject.Of(new IrVar(loc, name) { Type = value.Type }, type);
    }

    private IrExpr WithPrelude(IrLoc loc, ImmutableArray<IrStmt>.Builder prelude, IrExpr value) =>
        prelude.Count == 0 ? value : new IrStmtExpr(loc, prelude.ToImmutable(), value) { Type = value.Type };

    /// <summary>R21.3. <c>e is P</c>.</summary>
    private IrExpr LowerIsPattern(IsPatternExpressionSyntax node, IrLoc loc)
    {
        var prelude = ImmutableArray.CreateBuilder<IrStmt>();
        var subject = PatternSubject(node.Expression, prelude);
        var cond = Pattern(node.Pattern, subject);
        return WithPrelude(loc, prelude, cond with { Type = Bool });
    }

    /// <summary>
    /// R21.4. A switch expression is a chain of conditionals, one per arm, tried in order.
    /// When no arm matches, C# throws <c>SwitchExpressionException</c>; so does the
    /// translation, and a method that does not declare it must prove that it cannot.
    /// </summary>
    private IrExpr LowerSwitchExpression(SwitchExpressionSyntax node, IrLoc loc)
    {
        var prelude = ImmutableArray.CreateBuilder<IrStmt>();
        var subject = PatternSubject(node.GoverningExpression, prelude);
        var type = known.MapType(model.GetTypeInfo(node).ConvertedType ?? model.GetTypeInfo(node).Type);

        var arms = new List<(IrExpr Cond, IrExpr Body)>();
        foreach (var arm in node.Arms)
        {
            var cond = Pattern(arm.Pattern, subject);
            if (arm.WhenClause is { } when) cond = Conj(Locations.From(when), cond, Lower(when.Condition));
            arms.Add((cond, ToArmType(Lower(arm.Expression), type)));
        }

        IrExpr result = arms.Count > 0 && IsTrue(arms[^1].Cond)
            ? arms[^1].Body
            : new IrRaise(loc, LibraryException(loc, "System.Runtime.CompilerServices.SwitchExpressionException")) { Type = type };
        for (var i = arms.Count - 1 - (arms.Count > 0 && IsTrue(arms[^1].Cond) ? 1 : 0); i >= 0; i--)
            result = IsTrue(arms[i].Cond)
                ? arms[i].Body
                : new IrConditional(arms[i].Body.Loc, arms[i].Cond, arms[i].Body, result) { Type = type };
        return WithPrelude(loc, prelude, result with { Type = type });
    }

    /// <summary>
    /// A target-typed switch converts each arm to the switch's type, but Roslyn reports
    /// no conversion on the arm itself; the one that matters, <c>T</c> to <c>T?</c>, is
    /// applied here.
    /// </summary>
    private static IrExpr ToArmType(IrExpr body, IrType? type) =>
        body is IrRaise { Type: null } raise ? raise with { Type = type } :
        type is IrOptionType option && body is not IrNull && body is not IrRaise &&
        body.Type is not null and not IrOptionType
            ? new IrOptionOp(body.Loc, OptionOpKind.Some, body) { Type = option }
            : body;

    /// <summary>R21.6. <c>e as C</c>: <c>e</c> when it is a <c>C</c>, and <c>null</c> otherwise.</summary>
    private IrExpr LowerAs(BinaryExpressionSyntax node, IrLoc loc)
    {
        if (model.GetTypeInfo(node.Right).Type is not { } target) return Unsupported(node, loc);
        var mapped = known.MapType(model.GetTypeInfo(node).Type);
        var prelude = ImmutableArray.CreateBuilder<IrStmt>();
        // R27.46. On an object of a class translated at its exact type, `as` is decided
        // statically: the object, or `null`.
        if (mapped is IrClassType { Nullable: true } nullableClass)
        {
            var exactSubject = PatternSubject(node.Left, prelude);
            if (ExactClassType(exactSubject.Type) is null) return Unsupported(node, loc);
            var test = TypeTest(node, target, exactSubject, out var same);
            return WithPrelude(loc, prelude, IsFalse(test)
                ? new IrNull(loc) { Type = nullableClass }
                : same with { Type = nullableClass });
        }
        if (mapped is not IrOptionType result) return Unsupported(node, loc);
        var subject = PatternSubject(node.Left, prelude);
        var cond = TypeTest(node, target, subject, out var narrowed);
        if (IsFalse(cond)) return WithPrelude(loc, prelude, new IrNull(loc) { Type = result });
        if (IsTrue(cond) && narrowed.Type is not IrOptionType && result.Inner.Equals(narrowed.Type))
            return WithPrelude(loc, prelude, new IrOptionOp(loc, OptionOpKind.Some, narrowed) { Type = result });
        var conditional = new IrConditional(loc, cond,
            new IrOptionOp(loc, OptionOpKind.Some, narrowed) { Type = result },
            new IrNull(loc) { Type = result }) { Type = result };
        return WithPrelude(loc, prelude, conditional);
    }

    /// <summary>The condition under which <paramref name="pattern"/> matches.</summary>
    private IrExpr Pattern(PatternSyntax pattern, Subject subject)
    {
        var loc = Locations.From(pattern);
        switch (pattern)
        {
            case DiscardPatternSyntax:
                return True(loc);

            case ParenthesizedPatternSyntax p:
                return Pattern(p.Pattern, subject);

            case VarPatternSyntax v when subject.Value is { } value:
                return Bind(v.Designation, value, loc);

            case UnaryPatternSyntax u when u.OperatorToken.IsKind(SyntaxKind.NotKeyword):
                return new IrUnary(loc, UnOp.Not, Pattern(u.Pattern, subject)) { Type = Bool };

            case BinaryPatternSyntax b:
                return new IrBinary(loc,
                    b.OperatorToken.IsKind(SyntaxKind.AndKeyword) ? BinOp.And : BinOp.Or,
                    Pattern(b.Left, subject), Pattern(b.Right, subject)) { Type = Bool };

            // `case T.U =>`: the parser cannot tell a type from a constant; the binder can.
            case ConstantPatternSyntax c when subject.Value is not null &&
                                              model.GetSymbolInfo(c.Expression).Symbol is ITypeSymbol ct:
                return TypeTest(c, ct, subject, out _);

            case ConstantPatternSyntax c when subject.Value is { } value:
                return ConstantTest(c, value);

            case RelationalPatternSyntax r when subject.Value is { } value:
            {
                var op = r.OperatorToken.Kind() switch
                {
                    SyntaxKind.LessThanToken => BinOp.Lt,
                    SyntaxKind.LessThanEqualsToken => BinOp.Le,
                    SyntaxKind.GreaterThanToken => BinOp.Gt,
                    _ => BinOp.Ge,
                };
                return new IrBinary(loc, op, NonNull(value), Lower(r.Expression)) { Type = Bool };
            }

            case TypePatternSyntax t when subject.Value is not null &&
                                          model.GetTypeInfo(t.Type).Type is { } tt:
                return TypeTest(t, tt, subject, out _);

            case DeclarationPatternSyntax d when subject.Value is not null &&
                                                 model.GetTypeInfo(d.Type).Type is { } dt:
            {
                var cond = TypeTest(d, dt, subject, out var narrowed);
                return Conj(loc, cond, Bind(d.Designation, narrowed, loc));
            }

            case RecursivePatternSyntax r:
                return Recursive(r, subject, loc);

            default:
                return UnsupportedPattern(pattern, loc);
        }
    }

    private IrExpr Recursive(RecursivePatternSyntax r, Subject subject, IrLoc loc)
    {
        // A positional pattern over a tuple literal matches it component by component.
        if (subject.Value is null)
        {
            if (r.Type is not null || r.PropertyPatternClause is not null || r.Designation is not null ||
                r.PositionalPatternClause is not { } tuple ||
                tuple.Subpatterns.Count != subject.Components.Length)
                return UnsupportedPattern(r, loc);
            var all = True(loc);
            for (var i = 0; i < tuple.Subpatterns.Count; i++)
                all = Conj(loc, all, Pattern(tuple.Subpatterns[i].Pattern, subject.Components[i]));
            return all;
        }

        // `T { … }` tests the type; `{ … }` alone tests that the subject is not null.
        IrExpr cond;
        IrExpr narrowed;
        var type = subject.Type;
        if (r.Type is not null && model.GetTypeInfo(r.Type).Type is { } rt)
        {
            cond = TypeTest(r, rt, subject, out narrowed);
            type = rt;
        }
        else if (subject.Value.Type is IrOptionType)
        {
            cond = new IrOptionOp(loc, OptionOpKind.HasValue, subject.Value) { Type = Bool };
            narrowed = NonNull(subject.Value);
        }
        else
        {
            cond = True(loc);
            narrowed = subject.Value;
        }

        if (r.PositionalPatternClause is not null) return UnsupportedPattern(r, loc);

        if (r.PropertyPatternClause is { } props)
        {
            foreach (var sub in props.Subpatterns)
            {
                var member = sub.NameColon is { } nc
                    ? model.GetSymbolInfo(nc.Name).Symbol
                    : sub.ExpressionColon is { } ec ? model.GetSymbolInfo(ec.Expression).Symbol : null;
                if (member is not IPropertySymbol prop || MemberRead(prop, narrowed, loc) is not { } read)
                {
                    diagnostics.Unsupported(Locations.From(sub), $"the property pattern `{sub}`");
                    continue;
                }
                cond = Conj(loc, cond, Pattern(sub.Pattern, Subject.Of(read, prop.Type)));
            }
        }

        if (r.Designation is { } designation) cond = Conj(loc, cond, Bind(designation, narrowed, loc));
        return cond;
    }

    private IrExpr UnsupportedPattern(PatternSyntax pattern, IrLoc loc)
    {
        diagnostics.Unsupported(loc, $"The pattern `{pattern}`");
        return new IrLiteral(loc, false) { Type = Bool };
    }

    /// <summary>
    /// R21.3. A pattern variable is bound to the value it names. The binding is a
    /// substitution, so the variable costs nothing and reads exactly what was tested.
    /// </summary>
    private IrExpr Bind(VariableDesignationSyntax designation, IrExpr value, IrLoc loc)
    {
        switch (designation)
        {
            case DiscardDesignationSyntax:
                return True(loc);
            case SingleVariableDesignationSyntax single when model.GetDeclaredSymbol(single) is { } local:
                _patternBindings[local] = value;
                return True(loc);
            default:
                diagnostics.Unsupported(loc, $"the designation `{designation}`");
                return True(loc);
        }
    }

    private IrExpr ConstantTest(ConstantPatternSyntax c, IrExpr value)
    {
        var loc = Locations.From(c);
        if (c.Expression.IsKind(SyntaxKind.NullLiteralExpression))
            return Sorted.HasOpaqueNull(value.Type)
                ? Sorted.IsNull(loc, value)
                : value.Type is IrOptionType
                ? new IrUnary(loc, UnOp.Not, new IrOptionOp(loc, OptionOpKind.HasValue, value) { Type = Bool }) { Type = Bool }
                // R25.4, R24.23. A type parameter may be instantiated at a reference type.
                : Sorted.HasOpaqueNull(value.Type) ? Sorted.IsNull(loc, value)
                : new IrLiteral(loc, false) { Type = Bool };

        // R21.8. A constant of a `[SpecType]` enum is a constructor: its discriminator.
        if (model.GetSymbolInfo(c.Expression).Symbol is IFieldSymbol f && known.CaseConstructor(f) is { } ctor)
            return new IrSpecOp(loc, ctor + "?", [NonNull(value)]) { Type = Bool };

        var constant = Lower(c.Expression);
        return new IrBinary(loc, BinOp.Eq, value, constant) { Type = Bool };
    }

    /// <summary>
    /// R21.3. The subject is a <paramref name="target"/>: not null, and, when the target is
    /// a case of the subject's closed hierarchy, built by that case's constructor.
    /// </summary>
    private IrExpr TypeTest(SyntaxNode at, ITypeSymbol target, Subject subject, out IrExpr narrowed)
    {
        var loc = Locations.From(at);
        var value = subject.Value!;
        IrExpr cond = True(loc);
        if (value.Type is IrOptionType)
            cond = new IrOptionOp(loc, OptionOpKind.HasValue, value) { Type = Bool };
        narrowed = NonNull(value);

        if (subject.Type is { } from && SymbolEqualityComparer.Default.Equals(
                from.WithNullableAnnotation(NullableAnnotation.NotAnnotated),
                target.WithNullableAnnotation(NullableAnnotation.NotAnnotated)))
            return cond;

        if (known.CaseConstructor(target) is { } ctor)
            return Conj(loc, cond, new IrSpecOp(loc, ctor + "?", [narrowed]) { Type = Bool });

        // R27.46. A translated class whose objects all have it as their dynamic type (R27.1)
        // is a `D` exactly when the class converts to `D`; the test is then the null test.
        if (ExactClassType(subject.Type) is { } exact)
            return model.Compilation.ClassifyCommonConversion(exact, target) is { IsImplicit: true, IsReference: true } or { IsIdentity: true }
                ? cond
                : False(loc);

        diagnostics.Error("PALCS0627", loc,
            $"A test that a `{subject.Type}` is a `{target}`. A type pattern translates when " +
            "the type is a case of the subject's closed record hierarchy, or the subject's " +
            "own type (doc/translation.md R21.3).");
        return cond;
    }

    /// <summary>
    /// R21.2. A property of a case record read off a value of it: the projection of the
    /// component it holds. A <c>[SpecOp]</c> on the property says otherwise.
    /// </summary>
    private IrExpr? MemberRead(IPropertySymbol prop, IrExpr value, IrLoc loc)
    {
        if (known.SpecOpName(prop) is { } op)
            return new IrSpecOp(loc, op, [value]) { Type = known.MapType(prop.Type) };
        return Projection(prop, value, loc);
    }

    private IrExpr? Projection(IPropertySymbol prop, IrExpr value, IrLoc loc)
    {
        var owner = prop.ContainingType;
        var index = known.CaseComponentIndex(prop);
        if (index < 0 || known.CaseConstructor(owner) is not { } ctor ||
            known.SpecTypeName(owner) is not { } spec)
            return null;
        var arity = known.CaseComponents(owner).Length;
        var pats = string.Join(" ", Enumerable.Range(0, arity).Select(i => i == index ? "__pal_v" : "_"));
        var fn = $"(fun (__pal_x:{spec}{{{ctor}? __pal_x}}) -> match __pal_x with | {ctor} {pats} -> __pal_v)";
        return new IrSpecOp(loc, fn, [NonNull(value)]) { Type = known.MapType(prop.Type) };
    }

    /// <summary>
    /// R21.7. An exception the BCL declares. It is a value of <c>exn</c> that records its
    /// class's name and nothing else: the message and the parameter name a program passes
    /// are not modelled, since no verified code can observe them.
    /// </summary>
    internal IrExpr LibraryException(IrLoc loc, string type) =>
        new IrSpecOp(loc, "Pulse.Lib.CSharp.Exn.BclException",
            [new IrLiteral(loc, type) { Type = new IrPrim(PrimKind.String) }]) { Type = new IrExnType(null) };
}
