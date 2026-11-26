using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Checked scalar/length slot obligations. They are ordinary postconditions:
/// unlike iterator protocol domains they must NOT broaden or restrict the
/// getter's authored preconditions or exceptional domain.
/// </summary>
internal static class EnumerationObservations
{
    internal sealed record Plan(IPropertySymbol Property, IPropertySymbol Observation, bool Length);

    public static Plan? Resolve(IMethodSymbol getter, WellKnown known, DiagnosticBag? diagnostics = null,
        INamedTypeSymbol? receiver = null)
    {
        if (getter.AssociatedSymbol is not IPropertySymbol property) return null;
        AttributeData? annotation = null;
        var declaration = property;
        for (var p = property; p is not null; p = p.OverriddenProperty)
        {
            annotation = p.GetAttributes().FirstOrDefault(a =>
                SymbolEqualityComparer.Default.Equals(a.AttributeClass, known.EnumerationObservationAttribute));
            if (annotation is not null) { declaration = p; break; }
        }
        if (annotation is null) return null;
        var name = Declarations.StringArgument(annotation, 0);
        var length = annotation.NamedArguments.Any(a => a.Key == "Length" && a.Value.Value is true);
        var receiverType = receiver ?? property.ContainingType;
        IPropertySymbol? observation = null;
        for (var c = declaration.ContainingType; c is not null && observation is null; c = c.BaseType)
            observation = c.GetMembers(name ?? "").OfType<IPropertySymbol>().FirstOrDefault();
        if (observation?.GetMethod is { } specGetter &&
            NominalDispatch.ClassSlot(receiverType, specGetter)?.AssociatedSymbol is IPropertySymbol actual)
            observation = actual;
        // The generated law is bound at this getter's receiver type. A hidden
        // spec member of the same name would bind a different observation.
        IPropertySymbol? visible = null;
        for (var c = receiverType; c is not null && visible is null; c = c.BaseType)
            visible = c.GetMembers(name ?? "").OfType<IPropertySymbol>().FirstOrDefault();
        if (getter.MethodKind != MethodKind.PropertyGet || property.IsStatic ||
            !property.Parameters.IsEmpty || Declarations.Has(property, known.SpecAttribute) ||
            observation is null || observation.IsStatic || !observation.Parameters.IsEmpty ||
            !SymbolEqualityComparer.Default.Equals(visible, observation) ||
            !Declarations.Has(observation, known.SpecAttribute) ||
            name is null || !SyntaxFacts.IsValidIdentifier(name) ||
            (length
                ? property.Type.SpecialType != SpecialType.System_Int32 ||
                  known.MapType(observation.Type) is not IrSeqType
                : !SymbolEqualityComparer.Default.Equals(property.Type, observation.Type)))
        {
            diagnostics?.Error("PALCS0866", Locations.From(property.Locations.First().GetLineSpan()),
                "An [EnumerationObservation] getter must name a pure [Spec] property of the same type, " +
                "or a sequence observation with Length=true and an int result.");
            return null;
        }
        return new(property, observation, length);
    }

    public static ImmutableArray<string> Laws(IMethodSymbol method, WellKnown known,
        DiagnosticBag? diagnostics = null, INamedTypeSymbol? receiver = null)
    {
        if (Resolve(method, known, diagnostics, receiver) is not { } plan) return [];
        var observation = $"@this.{plan.Observation.Name}";
        return [
            plan.Length ? $"Result == {observation}.Length" : $"PalLang.Pal.Same(Result, {observation})",
            $"PalLang.Pal.Same({observation}, PalLang.Pal.Old({observation}))"
        ];
    }
}
