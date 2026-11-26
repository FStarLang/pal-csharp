using Microsoft.CodeAnalysis;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Nominal questions about a KNOWN runtime class. Callers must separately retain
/// evidence of that runtime class and its actual ownership representation.
/// These answers never authorize reusing a base invariant for a derived object.
/// </summary>
internal static class NominalDispatch
{
    // A reference-typed static source is not an exact runtime witness. In
    // particular, a disjoint nonsealed static class can have a matching subclass.
    public static bool? Assignable(INamedTypeSymbol exact, INamedTypeSymbol target)
    {
        if (exact.TypeKind != TypeKind.Class || target.TypeKind != TypeKind.Class)
            return null;
        bool uncertain = false;
        for (var c = exact; c is not null; c = c.BaseType)
        {
            var equal = EnumerableCasts.Classify(c, target);
            if (equal == true) return true;
            uncertain |= equal is null;
        }
        return uncertain ? null : false;
    }

    // Resolve the selected CLR class slot, not the most-derived member with the
    // same spelling. A `new` property does not override a base property.
    public static IMethodSymbol? ClassSlot(INamedTypeSymbol exact, IMethodSymbol slot)
    {
        if (slot.IsStatic || Assignable(exact, slot.ContainingType) != true)
            return null;
        for (var c = exact; c is not null; c = c.BaseType)
        foreach (var member in c.GetMembers())
        {
            var candidate = member switch {
                IMethodSymbol m => m,
                IPropertySymbol p when slot.MethodKind == MethodKind.PropertyGet => p.GetMethod,
                _ => null
            };
            for (var ancestor = candidate; ancestor is not null; ancestor = ancestor.OverriddenMethod)
                if (EnumerationProtocols.Same(ancestor, slot))
                    return candidate;
        }
        return null;
    }

    // Roslyn's actual interface map includes reimplementation. Never resolve an
    // interface slot by looking up a conveniently named public class method.
    public static IMethodSymbol? InterfaceSlot(INamedTypeSymbol exact, ISymbol slot) =>
        slot.ContainingType?.TypeKind != TypeKind.Interface ? null :
        exact.FindImplementationForInterfaceMember(slot) switch {
            IMethodSymbol m => m,
            IPropertySymbol p => p.GetMethod,
            _ => null
        };
}
