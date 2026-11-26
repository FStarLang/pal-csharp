using Microsoft.CodeAnalysis;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// A borrowing record can retain a known borrowing view as its owner. The
/// owner's identity is its state-cell reference, not its underlying collection.
/// Members are rechecked at this owner representation; no base invariant is
/// substituted for the view.
/// </summary>
internal static class BorrowedOwners
{
    internal sealed record Request(string Source, INamedTypeSymbol Struct,
        INamedTypeSymbol View, string Name);

    internal static IrNamedType Type(INamedTypeSymbol record, INamedTypeSymbol view, WellKnown known)
    {
        var ordinary = (IrNamedType)known.MapType(record)!;
        return ordinary with { Name = ordinary.Name + "_owner_" + view.Name };
    }

    internal static IrType Reference(BorrowContext view) =>
        new IrUserSpecType("BorrowedOwnerReference", "Pulse.Lib.Reference.ref", [view.StructType]);

    internal static string Demand(IMethodSymbol member, INamedTypeSymbol view, WellKnown known)
    {
        var source = Naming.Of(member.OriginalDefinition);
        var name = source + "_owner_" + view.Name;
        if (known.BorrowedOwnerSeen.Add(name))
            known.BorrowedOwnerDemand.Enqueue(new Request(source,
                member.ContainingType.OriginalDefinition, view.OriginalDefinition, name));
        return name;
    }
}
