using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>Attribute queries shared by the collector and the lowerers.</summary>
public static class Declarations
{
    public static bool Has(ISymbol symbol, INamedTypeSymbol attribute) =>
        symbol.GetAttributes().Any(a =>
            SymbolEqualityComparer.Default.Equals(a.AttributeClass, attribute));

    public static AttributeData? Find(ISymbol symbol, INamedTypeSymbol attribute) =>
        symbol.GetAttributes().FirstOrDefault(a =>
            SymbolEqualityComparer.Default.Equals(a.AttributeClass, attribute));

    public static ImmutableArray<AttributeData> All(ISymbol symbol, INamedTypeSymbol attribute) =>
        [.. symbol.GetAttributes().Where(a =>
            SymbolEqualityComparer.Default.Equals(a.AttributeClass, attribute))];

    /// <summary>The first string argument of an attribute application, if any.</summary>
    public static string? StringArgument(AttributeData data, int index = 0) =>
        data.ConstructorArguments.Length > index &&
        data.ConstructorArguments[index].Value is string s ? s : null;

    /// <summary>
    /// Which of the three kinds of translatable declaration a method is, or
    /// <c>null</c> if it is not translatable at all.
    /// </summary>
    public static CalleeKind? KindOf(IMethodSymbol method, WellKnown known)
    {
        if (Has(method, known.SpecAttribute)) return CalleeKind.Spec;
        if (Has(method, known.LemmaAttribute)) return CalleeKind.Lemma;
        if (method is { IsStatic: true, MethodKind: MethodKind.Ordinary }) return CalleeKind.Method;

        // §4.5. An instance method or constructor of a translated class: it carries the
        // object's invariant, which is what makes it translatable at all.
        return method is { IsStatic: false, MethodKind: MethodKind.Ordinary or MethodKind.Constructor }
               && method.ContainingType is { TypeKind: TypeKind.Class } owner
               && known.HasModel(owner)
            ? CalleeKind.Method
            : null;
    }

    /// <summary>
    /// Whether the member carries any annotation that only means something to pal-csharp.
    /// </summary>
    /// <remarks>
    /// This is what separates "the user did not ask us to translate this" from "the user
    /// asked and we cannot yet oblige". Only the second is a diagnostic — but it must be
    /// one, because a silently dropped contract is a proof that was never attempted and
    /// looks exactly like a proof that succeeded.
    /// </remarks>
    public static bool IsAnnotated(ISymbol symbol, WellKnown known) =>
        symbol.GetAttributes().Any(a =>
            a.AttributeClass is { ContainingNamespace.Name: WellKnown.Namespace });

    /// <summary>
    /// The syntactic location an attribute's argument occupies, so that a diagnostic
    /// about a spec string lands on the string rather than on the declaration.
    /// </summary>
    public static Location ArgumentLocation(AttributeData data, int index = 0)
    {
        if (data.ApplicationSyntaxReference?.GetSyntax()
                is Microsoft.CodeAnalysis.CSharp.Syntax.AttributeSyntax syntax &&
            syntax.ArgumentList is { } list && list.Arguments.Count > index)
        {
            return SpecBinder.ContentLocation(list.Arguments[index].Expression);
        }
        return data.ApplicationSyntaxReference?.GetSyntax().GetLocation() ?? Location.None;
    }

    public static ParamMode ModeOf(IParameterSymbol p) => p.RefKind switch
    {
        RefKind.Ref => ParamMode.Ref,
        RefKind.Out => ParamMode.Out,
        RefKind.In or RefKind.RefReadOnlyParameter => ParamMode.In,
        _ => ParamMode.Value,
    };
}
