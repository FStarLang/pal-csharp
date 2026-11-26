using Microsoft.CodeAnalysis;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Nominal eligibility for the reference-identity default-equality interpretation.
/// This deliberately does not infer equality behavior from a lowered Box type.
/// </summary>
internal static class DefaultEquality
{
    public static bool IsReferenceIdentity(INamedTypeSymbol type, WellKnown known)
    {
        if (type.TypeKind != TypeKind.Class || !type.IsSealed ||
            !known.IsPlainLike(type.OriginalDefinition) ||
            type.BaseType?.SpecialType != SpecialType.System_Object)
            return false;

        // EqualityComparer<T>.Default can select GenericEqualityComparer<T>.
        // Conservatively exclude every IEquatable<U> implementation, including
        // inherited and explicit implementations, not just a public Equals method.
        var equatable = known.Compilation.GetTypeByMetadataName("System.IEquatable`1");
        if (equatable is null || type.AllInterfaces.Any(i =>
                SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, equatable)))
            return false;

        // ObjectEqualityComparer<T> dispatches Object.Equals virtually. A new
        // overload is not an override; GetHashCode does not select equality.
        return !type.GetMembers("Equals").OfType<IMethodSymbol>()
            .Any(m => m.IsOverride);
    }
}
