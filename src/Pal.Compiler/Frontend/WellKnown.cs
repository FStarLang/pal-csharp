using Microsoft.CodeAnalysis;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Resolved symbols for everything in <c>Pal.Annotations</c> that the frontend must
/// recognise. Resolving once, by symbol, means recognition never depends on how the
/// user spelled a name (<c>Pal.Old</c>, <c>PalLang.Pal.Old</c>, or <c>Old</c> under a
/// <c>using static</c>) — only on what it binds to.
/// </summary>
public sealed class WellKnown
{
    public const string Namespace = "PalLang";

    private WellKnown(Compilation c)
    {
        INamedTypeSymbol Type(string name) =>
            c.GetTypeByMetadataName($"{Namespace}.{name}")
            ?? throw new InvalidOperationException(
                $"Pal.Annotations is not referenced: {Namespace}.{name} not found.");

        Pal = Type("Pal");
        Ghost = Type("Ghost`1");
        Seq = Type("Seq`1");
        SpecInt = Type("SpecInt");
        SpecNat = Type("SpecNat");
        SlProp = Type("SlProp");

        RequiresAttribute = Type("RequiresAttribute");
        EnsuresAttribute = Type("EnsuresAttribute");
        PreservesAttribute = Type("PreservesAttribute");
        PreservesValueAttribute = Type("PreservesValueAttribute");
        DecreasesAttribute = Type("DecreasesAttribute");
        ConsumesAttribute = Type("ConsumesAttribute");
        PlainAttribute = Type("PlainAttribute");
        FracAttribute = Type("FracAttribute");
        NonNullAttribute = Type("NonNullAttribute");
        RefineAttribute = Type("RefineAttribute");
        RefineAlwaysAttribute = Type("RefineAlwaysAttribute");
        SpecAttribute = Type("SpecAttribute");
        ModelAttribute = Type("ModelAttribute");
        InvariantAttribute = Type("InvariantAttribute");
        LemmaAttribute = Type("LemmaAttribute");
        PulseBodyAttribute = Type("PulseBodyAttribute");
        AdmitAttribute = Type("AdmitAttribute");
        GhostArgAttribute = Type("GhostArgAttribute");
        PulseTypeAttribute = Type("PulseTypeAttribute");
        IncludePulseAttribute = Type("IncludePulseAttribute");
    }

    public static WellKnown For(Compilation compilation) => new(compilation);

    public INamedTypeSymbol Pal { get; }
    public INamedTypeSymbol Ghost { get; }
    public INamedTypeSymbol Seq { get; }
    public INamedTypeSymbol SpecInt { get; }
    public INamedTypeSymbol SpecNat { get; }
    public INamedTypeSymbol SlProp { get; }

    public INamedTypeSymbol ModelAttribute { get; }
    public INamedTypeSymbol InvariantAttribute { get; }

    public INamedTypeSymbol RequiresAttribute { get; }
    public INamedTypeSymbol EnsuresAttribute { get; }
    public INamedTypeSymbol PreservesAttribute { get; }
    public INamedTypeSymbol PreservesValueAttribute { get; }
    public INamedTypeSymbol DecreasesAttribute { get; }
    public INamedTypeSymbol ConsumesAttribute { get; }
    public INamedTypeSymbol PlainAttribute { get; }
    public INamedTypeSymbol FracAttribute { get; }
    public INamedTypeSymbol NonNullAttribute { get; }
    public INamedTypeSymbol RefineAttribute { get; }
    public INamedTypeSymbol RefineAlwaysAttribute { get; }
    public INamedTypeSymbol SpecAttribute { get; }
    public INamedTypeSymbol LemmaAttribute { get; }
    public INamedTypeSymbol PulseBodyAttribute { get; }
    public INamedTypeSymbol AdmitAttribute { get; }
    public INamedTypeSymbol GhostArgAttribute { get; }
    public INamedTypeSymbol PulseTypeAttribute { get; }
    public INamedTypeSymbol IncludePulseAttribute { get; }

    /// <summary>True if <paramref name="symbol"/> is a member of the <c>Pal</c> intrinsics class.</summary>
    public bool IsPalIntrinsic(ISymbol? symbol) =>
        symbol is not null &&
        SymbolEqualityComparer.Default.Equals(symbol.ContainingType?.OriginalDefinition, Pal);

    public bool IsGhost(ITypeSymbol? t) => IsConstructedFrom(t, Ghost);
    public bool IsSeq(ITypeSymbol? t) => IsConstructedFrom(t, Seq);

    private static bool IsConstructedFrom(ITypeSymbol? t, INamedTypeSymbol def) =>
        t is INamedTypeSymbol n &&
        SymbolEqualityComparer.Default.Equals(n.OriginalDefinition, def);

    /// <summary>The C# scalar-to-Pulse mapping of <c>doc/translation.md</c> §3 (R3.1).</summary>
    /// <summary>Whether a class declares the <c>[Model]</c> member R3.9 requires.</summary>
    public bool HasModel(INamedTypeSymbol type) =>
        type.GetMembers().Any(m => Declarations.Has(m, ModelAttribute));

    public IrType? MapType(ITypeSymbol? type)
    {
        switch (type)
        {
            case null:
                return null;
            case IArrayTypeSymbol { Rank: 1 } array when MapType(array.ElementType) is { } e:
                return new IrArrayType(e);
            case INamedTypeSymbol named when IsSeq(named) && MapType(named.TypeArguments[0]) is { } se:
                return new IrSeqType(se);
            case INamedTypeSymbol named when IsGhost(named) && MapType(named.TypeArguments[0]) is { } ge:
                return new IrGhostType(ge);
            // §3.4. A class is translated exactly when it declares a [Model] member: R3.9
            // makes the model mandatory, so its presence is the same test as "annotated".
            case INamedTypeSymbol { TypeKind: TypeKind.Class } named when HasModel(named):
                return new IrClassType(named.Name);
        }

        if (SymbolEqualityComparer.Default.Equals(type, SpecInt)) return new IrPrim(PrimKind.SpecInt);
        if (SymbolEqualityComparer.Default.Equals(type, SpecNat)) return new IrPrim(PrimKind.SpecNat);
        if (SymbolEqualityComparer.Default.Equals(type, SlProp)) return new IrPrim(PrimKind.SlProp);

        return type.SpecialType switch
        {
            SpecialType.System_Void => IrPrim.Void,
            SpecialType.System_Boolean => IrPrim.Bool,
            SpecialType.System_SByte => new IrPrim(PrimKind.SByte),
            SpecialType.System_Byte => new IrPrim(PrimKind.Byte),
            SpecialType.System_Int16 => new IrPrim(PrimKind.Short),
            SpecialType.System_UInt16 => new IrPrim(PrimKind.UShort),
            SpecialType.System_Int32 => new IrPrim(PrimKind.Int),
            SpecialType.System_UInt32 => new IrPrim(PrimKind.UInt),
            SpecialType.System_Int64 => new IrPrim(PrimKind.Long),
            SpecialType.System_UInt64 => new IrPrim(PrimKind.ULong),
            SpecialType.System_Char => new IrPrim(PrimKind.Char),
            _ => type.TypeKind == TypeKind.Struct ? new IrNamedType(type.Name) : null,
        };
    }
}
