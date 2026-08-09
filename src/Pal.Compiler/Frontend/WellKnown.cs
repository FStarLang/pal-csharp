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
        IncludePulseFileAttribute = Type("IncludePulseFileAttribute");
        BackwardAttribute = Type("BackwardAttribute");
        SpecTypeAttribute = Type("SpecTypeAttribute");
        SpecOpAttribute = Type("SpecOpAttribute");
        SpecCtorAttribute = Type("SpecCtorAttribute");

        // R17.1. `Span<T>` and `ReadOnlySpan<T>` are BCL types, not pal-csharp ones, so
        // they are looked up by metadata name and are allowed to be absent: a host whose
        // framework does not define them is a host on which no program mentions them.
        Span = c.GetTypeByMetadataName("System.Span`1");
        ReadOnlySpan = c.GetTypeByMetadataName("System.ReadOnlySpan`1");
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
    public INamedTypeSymbol IncludePulseFileAttribute { get; }
    public INamedTypeSymbol BackwardAttribute { get; }
    public INamedTypeSymbol SpecTypeAttribute { get; }
    public INamedTypeSymbol SpecOpAttribute { get; }
    public INamedTypeSymbol SpecCtorAttribute { get; }

    /// <summary>R17.1. <c>System.Span&lt;T&gt;</c>, or null where the framework has none.</summary>
    public INamedTypeSymbol? Span { get; }

    /// <summary>R17.1. <c>System.ReadOnlySpan&lt;T&gt;</c>, or null where the framework has none.</summary>
    public INamedTypeSymbol? ReadOnlySpan { get; }

    /// <summary>True if <paramref name="symbol"/> is a member of the <c>Pal</c> intrinsics class.</summary>
    public bool IsPalIntrinsic(ISymbol? symbol) =>
        symbol is not null &&
        SymbolEqualityComparer.Default.Equals(symbol.ContainingType?.OriginalDefinition, Pal);

    public bool IsGhost(ITypeSymbol? t) => IsConstructedFrom(t, Ghost);
    public bool IsSeq(ITypeSymbol? t) => IsConstructedFrom(t, Seq);
    public bool IsSpecList(ITypeSymbol? t) => IsConstructedFrom(t, SpecList);

    /// <summary>R17.1. A <c>Span&lt;T&gt;</c>, which is the *writable* array slot.</summary>
    public bool IsSpan(ITypeSymbol? t) => Span is not null && IsConstructedFrom(t, Span);

    /// <summary>R17.2. A <c>ReadOnlySpan&lt;T&gt;</c>, which is the *fractional* array slot.</summary>
    public bool IsReadOnlySpan(ITypeSymbol? t) =>
        ReadOnlySpan is not null && IsConstructedFrom(t, ReadOnlySpan);

    /// <summary>Either span. R17.1 translates both to the same thing.</summary>
    public bool IsAnySpan(ITypeSymbol? t) => IsSpan(t) || IsReadOnlySpan(t);

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
    /// <summary>
    /// R9.21b. A class is translated exactly when it has an abstraction function — its
    /// own, or the one it inherits with the representation of an open base. The walk stops
    /// at an `abstract` or `sealed` base: an abstract class's model is abstract, so R9.6
    /// makes every subclass supply its own, and a sealed one cannot be derived from.
    /// </summary>
    public bool HasModel(INamedTypeSymbol type)
    {
        for (var t = type; t is not null; t = t.BaseType)
        {
            if (t.GetMembers().Any(m => Declarations.Has(m, ModelAttribute))) return true;
            if (!SymbolEqualityComparer.Default.Equals(t, type) && (t.IsAbstract || t.IsSealed))
                return false;
            if (t.BaseType is not { IsAbstract: false, IsSealed: false }) return false;
        }
        return false;
    }

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

    /// <summary>
    /// R14.1. Whether a type parameter carries no constraint at all. Every kind of
    /// constraint is checked, not only the ones with a keyword: a base type or interface
    /// (<c>ConstraintTypes</c>), <c>class</c>, <c>struct</c>, <c>new()</c>,
    /// <c>notnull</c> and <c>unmanaged</c>. Each says something about <c>T</c> that the
    /// translation would have to carry, and none has been probed.
    /// </summary>
    public static bool Unconstrained(ITypeParameterSymbol tp) =>
        tp.ConstraintTypes.IsEmpty &&
        !tp.HasReferenceTypeConstraint &&
        !tp.HasValueTypeConstraint &&
        !tp.HasConstructorConstraint &&
        !tp.HasNotNullConstraint &&
        !tp.HasUnmanagedTypeConstraint;

    /// <summary>
    /// R14.5. A call's resolved type arguments, in declaration order. Roslyn has already
    /// resolved them — inferred and explicit calls are indistinguishable here, which is
    /// why they translate identically. An argument this cannot map yields no arguments at
    /// all, so that the type is reported where it is rejected rather than twice.
    /// </summary>
    public ImmutableArray<IrType> TypeArguments(IMethodSymbol method)
    {
        // R15.1. The declaring type's arguments come first, matching the order the
        // callee's binders were emitted in: a method of `Node<T>` is a function of `T`
        // exactly as a generic method is a function of the parameter it declares itself.
        var all = method.ContainingType is { TypeArguments.IsEmpty: false } owner
            ? owner.TypeArguments.AddRange(method.TypeArguments)
            : method.TypeArguments;
        if (all.IsEmpty) return ImmutableArray<IrType>.Empty;
        var mapped = ImmutableArray.CreateBuilder<IrType>();
        foreach (var a in all)
        {
            if (MapType(a) is not { } t) return ImmutableArray<IrType>.Empty;
            mapped.Add(t);
        }
        return mapped.ToImmutable();
    }

    public IrType? MapType(ITypeSymbol? type)
    {
        switch (type)
        {
            case null:
                return null;
            case IArrayTypeSymbol { Rank: 1 } array when MapType(array.ElementType) is { } e:
                return new IrArrayType(e);
            // R14.1/R14.4. An *unconstrained* type parameter is a type like any other. A
            // constrained one is not mapped here: the constraint is a typeclass obligation
            // the scheme does not carry, and R14.1 refuses it with PALCS0580 rather than
            // translate it with the constraint dropped.
            case ITypeParameterSymbol tp when Unconstrained(tp):
                return new IrTypeParamType(tp.Name);
            // R17.1. A span is a *borrowed window*, and that is a slot kind of its own:
            // `Pulse.Lib.Slice.slice`, with `S.pts_to` for its contents. It is not the
            // array slot. Identifying the two would make the implicit `T[]` -> `Span<T>`
            // conversion emit nothing, which is tempting and wrong: it works only for a
            // span that is the whole of exactly one array, and the point of a span is that
            // it need not be. Being its own type is what lets `a.AsSpan(i, n)` translate
            // (R17.5) and lets a method taking `Span<T>` be called with a window.
            case INamedTypeSymbol named when IsAnySpan(named) &&
                                             MapType(named.TypeArguments[0]) is { } spanElement:
                return new IrSpanType(spanElement);
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
            // R10.2. `C?` is the nullable pointer and `C` is its non-null refinement, and
            // the annotation is part of the type: it is what makes the base case of R10.3's
            // induction reachable by the prover.
            // R12.1. A `[Plain]` class is translated too, and is translated for the same
            // reason: it has a representation. What it does not have is a model, so it is
            // recognised by the attribute rather than by the `[Model]` member.
            case INamedTypeSymbol { TypeKind: TypeKind.Class } named
                when HasModel(named) || Declarations.Has(named.OriginalDefinition, PlainAttribute):
            {
                // R15.3. A constructed generic class carries its resolved arguments. An
                // argument this cannot map makes the whole type unmappable, so the
                // refusal lands on the class type rather than silently dropping a
                // parameter and emitting a term with a free variable in it.
                var classArgs = ImmutableArray.CreateBuilder<IrType>();
                foreach (var a in named.TypeArguments)
                {
                    if (MapType(a) is not { } mapped) return null;
                    classArgs.Add(mapped);
                }
                return new IrClassType(named.Name, named.NullableAnnotation == NullableAnnotation.Annotated)
                {
                    Plain = Declarations.Has(named.OriginalDefinition, PlainAttribute),
                    TypeArguments = classArgs.ToImmutable(),
                };
            }
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
