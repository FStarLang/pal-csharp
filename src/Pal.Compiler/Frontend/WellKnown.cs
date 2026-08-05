using System.Collections.Immutable;
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
        SpecList = Type("SpecList`1");
        SpecListOps = Type("SpecList");

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
        BackwardAttribute = Type("BackwardAttribute");
        SpecTypeAttribute = Type("SpecTypeAttribute");
        SpecOpAttribute = Type("SpecOpAttribute");
        SpecCtorAttribute = Type("SpecCtorAttribute");
    }

    public static WellKnown For(Compilation compilation) => new(compilation);

    public INamedTypeSymbol Pal { get; }
    public INamedTypeSymbol Ghost { get; }
    public INamedTypeSymbol Seq { get; }
    public INamedTypeSymbol SpecInt { get; }
    public INamedTypeSymbol SpecNat { get; }
    public INamedTypeSymbol SlProp { get; }
    public INamedTypeSymbol SpecList { get; }
    public INamedTypeSymbol SpecListOps { get; }

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
    public INamedTypeSymbol BackwardAttribute { get; }
    public INamedTypeSymbol SpecTypeAttribute { get; }
    public INamedTypeSymbol SpecOpAttribute { get; }
    public INamedTypeSymbol SpecCtorAttribute { get; }

    /// <summary>True if <paramref name="symbol"/> is a member of the <c>Pal</c> intrinsics class.</summary>
    public bool IsPalIntrinsic(ISymbol? symbol) =>
        symbol is not null &&
        SymbolEqualityComparer.Default.Equals(symbol.ContainingType?.OriginalDefinition, Pal);

    public bool IsGhost(ITypeSymbol? t) => IsConstructedFrom(t, Ghost);
    public bool IsSeq(ITypeSymbol? t) => IsConstructedFrom(t, Seq);
    public bool IsSpecList(ITypeSymbol? t) => IsConstructedFrom(t, SpecList);

    /// <summary>
    /// R11.1. The F* type a <c>[SpecType]</c> denotes, or null if this is not one. This is
    /// the whole of what the translator knows about a user's specification type.
    /// </summary>
    public string? SpecTypeName(ITypeSymbol? t) =>
        t is INamedTypeSymbol n &&
        Declarations.StringArgument(n.OriginalDefinition, SpecTypeAttribute) is { } name
            ? name
            : null;

    /// <summary>R11.2. The F* term a <c>[SpecOp]</c> member denotes.</summary>
    public string? SpecOpName(ISymbol? m) =>
        m is not null ? Declarations.StringArgument(m, SpecOpAttribute) : null;

    /// <summary>
    /// R11.1a. Whether this type is part of a <em>specification-type declaration</em>:
    /// it carries <c>[SpecType]</c>, or it declares the constructors and operations of one.
    ///
    /// <para>Such a type is not translated, and neither is any member of it. Its members
    /// have no bodies to translate — each says what it means in F* and throws — and its
    /// signatures mention specification-only types and open type parameters that no
    /// program method could. Recognising the declaration as a whole is what lets a user
    /// write one in an ordinary source file beside the code that uses it.</para>
    /// </summary>
    public bool IsSpecTypeDeclaration(INamedTypeSymbol? type) =>
        type is not null &&
        (SpecTypeName(type) is not null ||
         type.GetMembers().Any(m =>
             Declarations.Has(m, SpecOpAttribute) || Declarations.Has(m, SpecCtorAttribute)));

    /// <summary>R11.3. The F* constructor a <c>[SpecCtor]</c> method denotes.</summary>
    public string? SpecCtorName(ISymbol? m) =>
        m is not null ? Declarations.StringArgument(m, SpecCtorAttribute) : null;

    private static bool IsConstructedFrom(ITypeSymbol? t, INamedTypeSymbol def) =>
        t is INamedTypeSymbol n &&
        SymbolEqualityComparer.Default.Equals(n.OriginalDefinition, def);

    /// <summary>The C# scalar-to-Pulse mapping of <c>doc/translation.md</c> §3 (R3.1).</summary>
    /// <summary>Whether a class declares the <c>[Model]</c> member R3.9 requires.</summary>
    public bool HasModel(INamedTypeSymbol type) =>
        type.GetMembers().Any(m => Declarations.Has(m, ModelAttribute));

    /// <summary>
    /// R10.8. A class that holds a nullable reference of its own type. Recognising it here
    /// is syntactic on purpose: what it licenses — a client reaching a field of a node it
    /// has just null-tested — is a property of the *representation*, decided before any
    /// model is inverted.
    /// </summary>
    public static bool IsRecursive(INamedTypeSymbol type) =>
        type.GetMembers().OfType<IFieldSymbol>().Any(f =>
            !f.IsStatic &&
            SymbolEqualityComparer.Default.Equals(f.Type, type) &&
            f.NullableAnnotation == NullableAnnotation.Annotated);

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
            case INamedTypeSymbol named when IsSpecList(named) && MapType(named.TypeArguments[0]) is { } le:
                return new IrSpecListType(le);
            // R11.1. A user-declared specification type. It is tried before the class
            // rule because a `[SpecType]` may be a class, and before the struct rule
            // because it is usually a struct — it is not a representation either way.
            case INamedTypeSymbol named when SpecTypeName(named) is { } fstar:
            {
                var args = ImmutableArray.CreateBuilder<IrType>();
                foreach (var a in named.TypeArguments)
                {
                    if (MapType(a) is not { } mapped) return null;
                    args.Add(mapped);
                }
                return new IrUserSpecType(named.Name, fstar, args.ToImmutable());
            }
            // §3.4. A class is translated exactly when it declares a [Model] member: R3.9
            // makes the model mandatory, so its presence is the same test as "annotated".
            // R10.2. `C?` is `option C`, and the annotation is part of the type: it is what
            // makes the null test a pattern match, and hence what makes the base case of
            // R10.3's induction reachable by the prover.
            // R12.1. A `[Plain]` class is translated too, and is translated for the same
            // reason: it has a representation. What it does not have is a model, so it is
            // recognised by the attribute rather than by the `[Model]` member.
            case INamedTypeSymbol { TypeKind: TypeKind.Class } named
                when HasModel(named) || Declarations.Has(named.OriginalDefinition, PlainAttribute):
                return new IrClassType(named.Name, named.NullableAnnotation == NullableAnnotation.Annotated)
                {
                    Plain = Declarations.Has(named.OriginalDefinition, PlainAttribute),
                };
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
