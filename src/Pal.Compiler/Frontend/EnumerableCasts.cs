using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Target-relative adapters for directly object-derived model classes.
/// Sealed targets retain their concrete model; bounded nonsealed targets expose
/// checked observation slots over the actual source's ownership. No collection
/// implementation whitelist supplies dispatch evidence.
/// </summary>
internal static class EnumerableCasts
{
    public static bool Eligible(INamedTypeSymbol c, IrEnumerableType e, WellKnown known) =>
        c is { IsAbstract: false, TypeKind: TypeKind.Class } &&
        c.ContainingType is null &&
        c.BaseType?.SpecialType == SpecialType.System_Object &&
        !Declarations.Has(c, known.PlainAttribute) &&
        !Declarations.Has(c, known.RegionAttribute) &&
        HasProjection(c, e, known) &&
        (c.IsSealed || Schema(c, known) is not null);

    // A deliberately bounded schema. No member spelling or collection name is
    // privileged; all slots must have checked EnumerationObservation laws.
    public static IrEnumerationSchema? Schema(INamedTypeSymbol c, WellKnown known)
    {
        var plans = c.GetMembers().OfType<IPropertySymbol>()
            .Select(p => p.GetMethod is { } g ? EnumerationObservations.Resolve(g, known) : null)
            .Where(p => p is not null).Select(p => p!).ToArray();
        if (plans.Length != 2 || plans.Count(p => p.Length) != 1) return null;
        var length = plans.Single(p => p.Length);
        var scalar = plans.Single(p => !p.Length);
        if (length.Observation.Name != Projection(c, known) ||
            known.MapType(scalar.Property.Type) is not { } type ||
            !(type is IrPrim { Kind: PrimKind.Bool } || Sorted.IsComparer(type))) return null;
        return new(length.Property.Name, length.Observation.Name,
            scalar.Property.Name, scalar.Observation.Name, type) {
            Iteration = length.Observation.Type is INamedTypeSymbol { TypeArguments: [var element] }
                ? EnumerationProtocols.Schema(c, element, known) : null
        };
    }

    private static bool HasProjection(INamedTypeSymbol c, IrEnumerableType e, WellKnown known)
    {
        var marked = c.GetMembers().OfType<IPropertySymbol>()
            .Where(p => Declarations.Has(p, known.EnumerationModelAttribute)).ToArray();
        if (marked.Length != 0)
            return marked.Length == 1 && !marked[0].IsStatic && marked[0].Parameters.IsEmpty &&
                Declarations.Has(marked[0], known.SpecAttribute) &&
                known.MapType(marked[0].Type) is IrSeqType s && s.Element.Equals(e.Element);
        return c.GetMembers().OfType<IPropertySymbol>().Any(p =>
            Declarations.Has(p, known.ModelAttribute) &&
            known.MapType(p.Type) is IrSeqType s && s.Element.Equals(e.Element));
    }

    public static string? Projection(INamedTypeSymbol c, WellKnown known) =>
        c.GetMembers().OfType<IPropertySymbol>()
            .FirstOrDefault(p => Declarations.Has(p, known.EnumerationModelAttribute))?.Name;

    public static IrEnumerableType? ParameterType(IParameterSymbol p, WellKnown known)
    {
        return Target(p, known) is { } target &&
            known.MapType(p.Type) is IrEnumerableType e &&
            known.MapType(target) is IrClassType t
            ? e with { CastTarget = t with { Nullable = false }, CastProjection = Projection(target, known),
                Capability = target.IsSealed ? null : Schema(target, known) } : null;
    }

    public static bool SameClass(INamedTypeSymbol a, INamedTypeSymbol b) =>
        SymbolEqualityComparer.Default.Equals(a, b) ||
        a.DeclaringSyntaxReferences.Any(x => b.DeclaringSyntaxReferences.Any(y =>
            x.SyntaxTree == y.SyntaxTree && x.Span == y.Span)) &&
        a.TypeArguments.Length == b.TypeArguments.Length &&
        a.TypeArguments.Zip(b.TypeArguments, (x, y) =>
            SymbolEqualityComparer.Default.Equals(x, y) ||
            x is ITypeParameterSymbol xp && y is ITypeParameterSymbol yp &&
            xp.DeclaringSyntaxReferences.Any(r => yp.DeclaringSyntaxReferences.Any(s =>
                r.SyntaxTree == s.SyntaxTree && r.Span == s.Span))).All(x => x) &&
        (a.ContainingType is null ? b.ContainingType is null :
            b.ContainingType is not null && SameClass(a.ContainingType, b.ContainingType));

    private static bool SameDefinition(INamedTypeSymbol a, INamedTypeSymbol b) =>
        SymbolEqualityComparer.Default.Equals(a.OriginalDefinition, b.OriginalDefinition) ||
        a.DeclaringSyntaxReferences.Any(x => b.DeclaringSyntaxReferences.Any(y =>
            x.SyntaxTree == y.SyntaxTree && x.Span == y.Span));

    // C<T> is not known to miss C<int>: T may be instantiated with int.
    // Unequal compiler symbols are not evidence of unequal CLR runtime types.
    public static bool? Classify(INamedTypeSymbol source, INamedTypeSymbol target) =>
        SameClass(source, target) ? true :
        DefinitelyDifferent(source, target) ? false : null;

    private static bool DefinitelyDifferent(ITypeSymbol a, ITypeSymbol b) => (a, b) switch {
        (ITypeParameterSymbol, _) or (_, ITypeParameterSymbol) => false,
        (IArrayTypeSymbol x, IArrayTypeSymbol y) =>
            x.Rank != y.Rank || DefinitelyDifferent(x.ElementType, y.ElementType),
        (INamedTypeSymbol x, INamedTypeSymbol y) =>
            !SameDefinition(x, y) || x.TypeArguments.Zip(y.TypeArguments, DefinitelyDifferent).Any(x => x) ||
            x.ContainingType is { } xc && y.ContainingType is { } yc && DefinitelyDifferent(xc, yc),
        (IArrayTypeSymbol, INamedTypeSymbol) or (INamedTypeSymbol, IArrayTypeSymbol) => true,
        _ => false
    };

    public static INamedTypeSymbol? Target(IParameterSymbol p, WellKnown known)
    {
        if (Declarations.Has(p, known.ExactlyAttribute) ||
            known.MapType(p.Type) is not IrEnumerableType e ||
            p.ContainingSymbol is not IMethodSymbol method)
            return null;
        INamedTypeSymbol? target = null;
        foreach (var reference in method.DeclaringSyntaxReferences)
        {
            if (!known.Compilation.Owns(reference.SyntaxTree)) continue;
            var model = known.Compilation.Model(reference.SyntaxTree);
            foreach (var node in reference.GetSyntax().DescendantNodes())
            {
                var test = node switch {
                    IfStatementSyntax { Condition: IsPatternExpressionSyntax
                        { Expression: IdentifierNameSyntax subject, Pattern: DeclarationPatternSyntax d } } => (subject, d.Type),
                    VariableDeclaratorSyntax { Initializer.Value: BinaryExpressionSyntax
                        { RawKind: (int)Microsoft.CodeAnalysis.CSharp.SyntaxKind.AsExpression,
                          Left: IdentifierNameSyntax subject, Right: TypeSyntax type } } => (subject, type),
                    _ => ((IdentifierNameSyntax?)null, (TypeSyntax?)null)
                };
                if (test.Item1 is not { } id ||
                    model.GetSymbolInfo(id).Symbol is not IParameterSymbol found ||
                    found.Ordinal != p.Ordinal ||
                    !found.ContainingSymbol.DeclaringSyntaxReferences.Any(a =>
                        method.DeclaringSyntaxReferences.Any(b => a.SyntaxTree == b.SyntaxTree && a.Span == b.Span)) ||
                    model.GetTypeInfo(test.Item2!).Type is not INamedTypeSymbol c)
                    continue;
                c = (INamedTypeSymbol)Instantiate(c, (IMethodSymbol)found.ContainingSymbol, method, known);
                if (!Eligible(c, e, known) ||
                    target is not null && !SameClass(target, c))
                    return null;
                target = c;
            }
        }
        return target;
    }

    private static ITypeSymbol Instantiate(ITypeSymbol t, IMethodSymbol declaration, IMethodSymbol use, WellKnown known)
    {
        var bindings = declaration.TypeParameters.Zip(use.TypeArguments, (p, a) => (p, a))
            .Concat(declaration.ContainingType.TypeParameters.Zip(use.ContainingType.TypeArguments, (p, a) => (p, a)));
        foreach (var (p, a) in bindings)
            if (SymbolEqualityComparer.Default.Equals(t, p)) return a;
        return t switch {
            INamedTypeSymbol n when n.Arity > 0 => n.ConstructedFrom.Construct(
                n.TypeArguments.Select(a => Instantiate(a, declaration, use, known)).ToArray()),
            IArrayTypeSymbol a => known.Compilation.CreateArrayTypeSymbol(Instantiate(a.ElementType, declaration, use, known), a.Rank),
            _ => t
        };
    }

    public static ImmutableDictionary<string, IrEnumerableType> Parameters(IMethodSymbol m, WellKnown known) =>
        m.Parameters.Select(p => (p.Name, Type: ParameterType(p, known)))
            .Where(p => p.Type is not null).ToImmutableDictionary(p => p.Name, p => p.Type!);
}
