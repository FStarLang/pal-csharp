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
        Compilation = c;
        obliviousStrings = c.Options.NullableContextOptions == NullableContextOptions.Disable;
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
        ExactlyAttribute = Type("ExactlyAttribute");
        CallbackAttribute = Type("CallbackAttribute");
        SpecializeAttribute = Type("SpecializeAttribute");
        PlainAttribute = Type("PlainAttribute");
        RegionAttribute = Type("RegionAttribute");
        WrappingAttribute = Type("WrappingAttribute");
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
        RlimitAttribute = Type("RlimitAttribute");
        GhostArgAttribute = Type("GhostArgAttribute");
        PulseTypeAttribute = Type("PulseTypeAttribute");
        IncludePulseAttribute = Type("IncludePulseAttribute");
        IncludePulseFileAttribute = Type("IncludePulseFileAttribute");
        BackwardAttribute = Type("BackwardAttribute");
        SpecTypeAttribute = Type("SpecTypeAttribute");
        SpecOpAttribute = Type("SpecOpAttribute");
        RegionOpAttribute = Type("RegionOpAttribute");
        OpenAttribute = Type("OpenAttribute");
        SpecCtorAttribute = Type("SpecCtorAttribute");
        SpecCaseAttribute = Type("SpecCaseAttribute");
        SpecBindingAttribute = Type("SpecBindingAttribute");
        foreach (var binding in Declarations.All(c.Assembly, SpecBindingAttribute))
            if (Declarations.StringArgument(binding, 0) is { } member &&
                Declarations.StringArgument(binding, 1) is { } term)
                bindings[member] = term;
        ThrowsAttribute = Type("ThrowsAttribute");
        TranslateAnnotatedOnlyAttribute = Type("TranslateAnnotatedOnlyAttribute");
        AnnotatedOnly = Declarations.Has(c.Assembly, TranslateAnnotatedOnlyAttribute);
        Exception = c.GetTypeByMetadataName("System.Exception");

        // R17.1. `Span<T>` and `ReadOnlySpan<T>` are BCL types, not pal-csharp ones, so
        // they are looked up by metadata name and are allowed to be absent: a host whose
        // framework does not define them is a host on which no program mentions them.
        Span = c.GetTypeByMetadataName("System.Span`1");
        ReadOnlySpan = c.GetTypeByMetadataName("System.ReadOnlySpan`1");
    }

    // R20.9. Only a compilation with nullable reference types off (`--nullable disable`)
    // has oblivious strings. Elsewhere an unannotated `string` -- a contract's literal,
    // parsed apart from any `#nullable` context -- is the non-null `string` it is in code.
    private readonly bool obliviousStrings;

    public static WellKnown For(Compilation compilation) => new(compilation);

    public Compilation Compilation { get; }

    public INamedTypeSymbol Pal { get; }
    public INamedTypeSymbol Ghost { get; }
    public INamedTypeSymbol Seq { get; }
    public INamedTypeSymbol SpecInt { get; }
    public INamedTypeSymbol SpecNat { get; }
    public INamedTypeSymbol SlProp { get; }
    public INamedTypeSymbol SpecList { get; }
    public INamedTypeSymbol SpecListOps { get; }

    public INamedTypeSymbol ModelAttribute { get; }
    public INamedTypeSymbol ThrowsAttribute { get; }
    public INamedTypeSymbol TranslateAnnotatedOnlyAttribute { get; }

    /// <summary>
    /// R20.1. True when the assembly carries <c>[TranslateAnnotatedOnly]</c>: only the
    /// annotated declarations of the compilation are translated.
    /// </summary>
    public bool AnnotatedOnly { get; }

    /// <summary>R27.57. A replica the lowering has asked for: <c>Source</c> verified again at <c>At</c>.</summary>
    public sealed record ReplicaRequest(string Source, INamedTypeSymbol At, string Name);

    /// <summary>R27.57. The replica being lowered, while one is.</summary>
    public ReplicaRequest? Replica { get; set; }

    /// <summary>R27.57. Replicas asked for and not yet lowered.</summary>
    public Queue<ReplicaRequest> ReplicaDemand { get; } = new();
    public HashSet<string> ReplicaSeen { get; } = new(StringComparer.Ordinal);

    /// <summary>R35.18. A method translated at constant values of its <c>[Specialize]</c> parameters.</summary>
    public sealed record SpecializationRequest(string Source, string Name, ImmutableDictionary<string, bool> Values);

    /// <summary>R35.18. The specialization being lowered, while one is.</summary>
    public SpecializationRequest? Specialization { get; set; }

    /// <summary>R35.18. Specializations asked for and not yet lowered.</summary>
    public Queue<SpecializationRequest> SpecializationDemand { get; } = new();
    public HashSet<string> SpecializationSeen { get; } = new(StringComparer.Ordinal);

    /// <summary>R35.18. Whether a method has a <c>[Specialize]</c> parameter.</summary>
    public bool IsSpecialized(IMethodSymbol m) =>
        m.Parameters.Any(p => p.GetAttributes().Any(a => SymbolEqualityComparer.Default.Equals(a.AttributeClass, SpecializeAttribute)));
    public INamedTypeSymbol? Exception { get; }

    /// <summary>R19.1. <c>System.Exception</c> itself.</summary>
    public bool IsSystemException(ITypeSymbol? type) =>
        Exception is not null && SymbolEqualityComparer.Default.Equals(type, Exception);

    /// <summary>
    /// R19.1. A class this program declares that derives from <c>System.Exception</c>.
    /// Its values are F* <c>exn</c> payloads, not objects: it has no invariant, no model
    /// and no identity, and the constructor is a pure function of its arguments.
    /// </summary>
    private readonly HashSet<INamedTypeSymbol> skippedExceptions = new(SymbolEqualityComparer.Default);

    /// <summary>R20.1b. An exception class left untranslated under <c>[TranslateAnnotatedOnly]</c>.</summary>
    public void SkipException(INamedTypeSymbol symbol) => skippedExceptions.Add(symbol);

    public bool IsExceptionClass(ITypeSymbol? type)
    {
        if (type is not INamedTypeSymbol { TypeKind: TypeKind.Class } named) return false;
        if (named.DeclaringSyntaxReferences.IsEmpty) return false;
        if (skippedExceptions.Contains(named)) return false;
        for (var t = named.BaseType; t is not null; t = t.BaseType)
            if (IsSystemException(t)) return true;
        return false;
    }
    public INamedTypeSymbol InvariantAttribute { get; }

    public INamedTypeSymbol RequiresAttribute { get; }
    public INamedTypeSymbol EnsuresAttribute { get; }
    public INamedTypeSymbol PreservesAttribute { get; }
    public INamedTypeSymbol PreservesValueAttribute { get; }
    public INamedTypeSymbol DecreasesAttribute { get; }
    public INamedTypeSymbol ConsumesAttribute { get; }
    public INamedTypeSymbol ExactlyAttribute { get; }
    /// <summary>R27.39. <c>[Callback]</c>: a delegate parameter called with region pointers.</summary>
    public INamedTypeSymbol CallbackAttribute { get; }
    /// <summary>R35.18. <c>[Specialize]</c>: a <c>bool</c> parameter translated at each constant.</summary>
    public INamedTypeSymbol SpecializeAttribute { get; }
    public INamedTypeSymbol PlainAttribute { get; }

    /// <summary>R27.3. <c>[Region]</c>: a plain representation owned as one region.</summary>
    public INamedTypeSymbol RegionAttribute { get; }

    /// <summary>R12.1/R27.3. <c>[Plain]</c> or <c>[Region]</c>: a class with a representation and no model.</summary>
    public bool IsPlainLike(ISymbol symbol) =>
        Declarations.Has(symbol, PlainAttribute) || Declarations.Has(symbol, RegionAttribute);

    /// <summary>R27.16. A <c>[Region]</c> class, by its attribute's name (for callers without a <see cref="WellKnown"/>).</summary>
    public static bool IsRegionDeclaration(INamedTypeSymbol t) =>
        t.OriginalDefinition.GetAttributes().Any(a => a.AttributeClass?.Name == "RegionAttribute");

    /// <summary>R27.16. A <c>[Region]</c> class, whose annotated members are functions of the region.</summary>
    public bool IsRegionClass(ITypeSymbol? type) =>
        type is INamedTypeSymbol { TypeKind: TypeKind.Class } n && Declarations.Has(n.OriginalDefinition, RegionAttribute);

    /// <summary>R31.1. A <c>[Region(Cyclic = true)]</c> class.</summary>
    public bool IsCyclicRegionClass(ITypeSymbol? type) =>
        type is INamedTypeSymbol { TypeKind: TypeKind.Class } n &&
        Declarations.Find(n.OriginalDefinition, RegionAttribute) is { } data && Declarations.NamedFlag(data, "Cyclic");

    /// <summary>
    /// R31.2. The owner of a cyclic region: a class with a field of a cyclic region class
    /// that has a field of it in turn. A node's pointer to it is an identity, not ownership,
    /// so it is plain data wherever a region pointer is.
    /// </summary>
    public bool IsRingOwner(ITypeSymbol? type) =>
        type is INamedTypeSymbol { TypeKind: TypeKind.Class } c &&
        c.OriginalDefinition.GetMembers().OfType<IFieldSymbol>().Any(f =>
            IsCyclicRegionClass(f.Type) &&
            ((INamedTypeSymbol)f.Type).OriginalDefinition.GetMembers().OfType<IFieldSymbol>().Any(g =>
                SymbolEqualityComparer.Default.Equals(g.Type.OriginalDefinition, c.OriginalDefinition)));

    /// <summary>
    /// R27.3. The type arguments a class type carries: those of every enclosing type, then
    /// its own. A class nested in a generic class is generic in the outer parameters too.
    /// </summary>
    public static IEnumerable<ITypeSymbol> OuterAndOwnTypeArguments(INamedTypeSymbol named) =>
        (named.ContainingType is { } outer ? OuterAndOwnTypeArguments(outer) : []).Concat(named.TypeArguments);

    public static IEnumerable<ITypeParameterSymbol> OuterAndOwnTypeParameters(INamedTypeSymbol named) =>
        (named.ContainingType is { } outer ? OuterAndOwnTypeParameters(outer) : []).Concat(named.TypeParameters);
    public INamedTypeSymbol WrappingAttribute { get; }
    public INamedTypeSymbol FracAttribute { get; }
    public INamedTypeSymbol NonNullAttribute { get; }
    public INamedTypeSymbol RefineAttribute { get; }
    public INamedTypeSymbol RefineAlwaysAttribute { get; }
    public INamedTypeSymbol SpecAttribute { get; }
    public INamedTypeSymbol LemmaAttribute { get; }
    public INamedTypeSymbol PulseBodyAttribute { get; }
    public INamedTypeSymbol AdmitAttribute { get; }
    public INamedTypeSymbol RlimitAttribute { get; }
    public INamedTypeSymbol GhostArgAttribute { get; }
    public INamedTypeSymbol PulseTypeAttribute { get; }
    public INamedTypeSymbol IncludePulseAttribute { get; }
    public INamedTypeSymbol IncludePulseFileAttribute { get; }
    public INamedTypeSymbol BackwardAttribute { get; }
    public INamedTypeSymbol SpecTypeAttribute { get; }
    public INamedTypeSymbol SpecCaseAttribute { get; }
    public INamedTypeSymbol SpecBindingAttribute { get; }

    /// <summary>R21.5. <c>[assembly: SpecBinding]</c>s, by documentation-comment ID.</summary>
    private readonly Dictionary<string, string> bindings = new(StringComparer.Ordinal);

    /// <summary>R21.5. The F* term a library type or member is bound to, if any.</summary>
    public string? Binding(ISymbol? symbol) =>
        symbol?.OriginalDefinition.GetDocumentationCommentId() is { } id &&
        bindings.TryGetValue(id, out var term) ? term : null;
    public INamedTypeSymbol SpecOpAttribute { get; }

    /// <summary>R27.22. <c>[RegionOp]</c>: a specification operation over a region's nodes.</summary>
    public INamedTypeSymbol RegionOpAttribute { get; }

    /// <summary>R27.23. <c>[Open]</c>: a method run with its receiver's invariant unfolded.</summary>
    public INamedTypeSymbol OpenAttribute { get; }

    /// <summary>R27.22. The F* term a <c>[RegionOp]</c> method denotes, before the region's functions.</summary>
    public string? RegionOpName(ISymbol? m) =>
        m is not null ? Declarations.StringArgument(m, RegionOpAttribute) : null;
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
        t is INamedTypeSymbol n
            ? Declarations.StringArgument(n.OriginalDefinition, SpecTypeAttribute)
              ?? (CaseBase(n) is { } b ? SpecTypeName(b) : null)
              ?? Binding(n)
            : null;

    /// <summary>
    /// R20.11. Whether a <c>[SpecType]</c> is declared <c>Nullable = true</c>. A case of a
    /// closed hierarchy is as nullable as its base (R21.1), and a library reference type
    /// bound by R21.5 is nullable exactly where C# says it may be null.
    /// </summary>
    public bool IsNullableSpecType(ITypeSymbol? t) =>
        t is INamedTypeSymbol n &&
        (Declarations.Find(n.OriginalDefinition, SpecTypeAttribute) is { } data
            ? Declarations.NamedFlag(data, "Nullable")
            : CaseBase(n) is { } b
                ? IsNullableSpecType(b)
                : n.IsReferenceType && Binding(n) is not null);

    /// <summary>R11.2. The F* term a <c>[SpecOp]</c> member denotes.</summary>
    public string? SpecOpName(ISymbol? m) =>
        m is not null ? Declarations.StringArgument(m, SpecOpAttribute) ?? Binding(m) : null;

    /// <summary>
    /// R21.7. An exception class the BCL declares: one deriving from <c>System.Exception</c>
    /// that the program does not declare. Its values are <c>exn</c>s.
    /// </summary>
    public bool IsLibraryException(ITypeSymbol? t)
    {
        if (t is not INamedTypeSymbol n || n.Locations.Any(l => l.IsInSource)) return false;
        for (var b = n.BaseType; b is not null; b = b.BaseType)
            if (b.ToDisplayString() == "System.Exception") return true;
        return false;
    }

    /// <summary>
    /// R21.1. The base of a case of a closed hierarchy: <paramref name="t"/> is a sealed
    /// record whose direct base is an abstract record carrying <c>[SpecType]</c>.
    /// </summary>
    public INamedTypeSymbol? CaseBase(ITypeSymbol? t) =>
        t is INamedTypeSymbol { IsRecord: true, IsSealed: true, BaseType: { IsRecord: true, IsAbstract: true } b } &&
        Declarations.Has(b.OriginalDefinition, SpecTypeAttribute)
            ? b
            : null;

    /// <summary>
    /// R21.1. The F* data constructor of a case record or of a constant of a
    /// <c>[SpecType]</c> enum: its <c>[SpecCase]</c>, or else the constructor of that
    /// name in the F* module of the type it belongs to.
    /// </summary>
    public string? CaseConstructor(ISymbol? symbol)
    {
        INamedTypeSymbol? owner = symbol switch
        {
            INamedTypeSymbol n when CaseBase(n) is { } b => b,
            IFieldSymbol { ContainingType.TypeKind: TypeKind.Enum, HasConstantValue: true } f => f.ContainingType,
            _ => null,
        };
        if (owner is null || Declarations.StringArgument(owner.OriginalDefinition, SpecTypeAttribute) is not { } type)
            return null;
        if (Declarations.StringArgument(symbol!.OriginalDefinition, SpecCaseAttribute) is { } given) return given;
        var dot = type.LastIndexOf('.');
        return dot < 0 ? symbol.Name : type[..(dot + 1)] + symbol.Name;
    }

    /// <summary>
    /// R21.2. The components of a case record: the parameters of its one constructor, in
    /// order. Each is the argument of the F* constructor at its position, and the property
    /// of the same name (up to the case of its first letter) reads it back. Default when
    /// the record does not declare exactly one constructor besides its copy constructor.
    /// </summary>
    public ImmutableArray<IParameterSymbol> CaseComponents(INamedTypeSymbol c)
    {
        var ctors = c.InstanceConstructors
            .Where(m => !(m.Parameters.Length == 1 &&
                          SymbolEqualityComparer.Default.Equals(m.Parameters[0].Type, c)))
            .ToList();
        return ctors.Count == 1 ? ctors[0].Parameters : default;
    }

    /// <summary>R21.2. The position of a case record's property among its components.</summary>
    public int CaseComponentIndex(IPropertySymbol property)
    {
        if (CaseBase(property.ContainingType) is null) return -1;
        var components = CaseComponents(property.ContainingType);
        if (components.IsDefault) return -1;
        for (var i = 0; i < components.Length; i++)
            if (string.Equals(components[i].Name, property.Name, StringComparison.OrdinalIgnoreCase))
                return i;
        return -1;
    }

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
             Declarations.Has(m, SpecOpAttribute) || Declarations.Has(m, SpecCtorAttribute) ||
             Declarations.Has(m, RegionOpAttribute)));

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
    /// <summary>
    /// R27.46. The class an <c>[Exactly(typeof(C))]</c> parameter is an object of. An open
    /// generic is constructed by matching the interface it implements against the
    /// parameter's type: <c>C&lt;U&gt; : I&lt;U&gt;</c> at a parameter of type
    /// <c>I&lt;T&gt;</c> is <c>C&lt;T&gt;</c>. <c>null</c> when there is no attribute, or
    /// no such construction.
    /// </summary>
    public INamedTypeSymbol? ExactClass(IParameterSymbol p)
    {
        var attr = p.GetAttributes().FirstOrDefault(a => SymbolEqualityComparer.Default.Equals(a.AttributeClass, ExactlyAttribute));
        if (attr is null) return null;
        if (attr.ConstructorArguments is not [{ Value: INamedTypeSymbol named }]) return null;
        if (!named.IsUnboundGenericType) return named;
        var def = named.OriginalDefinition;
        if (p.Type is not INamedTypeSymbol param) return null;
        foreach (var i in def.AllInterfaces.Append(def.BaseType).OfType<INamedTypeSymbol>())
        {
            if (!SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, param.OriginalDefinition)) continue;
            var args = new ITypeSymbol?[def.TypeParameters.Length];
            for (var k = 0; k < i.TypeArguments.Length; k++)
                if (i.TypeArguments[k] is ITypeParameterSymbol tp && SymbolEqualityComparer.Default.Equals(tp.ContainingSymbol, def))
                    args[tp.Ordinal] = param.TypeArguments[k];
            if (args.All(a => a is not null)) return def.Construct(args!);
        }
        return null;
    }

    public bool HasModel(INamedTypeSymbol type)
    {
        // R27.3. A `[Region]` class's `[Model]` is the view of one node, not an object
        // model: its objects are cells of their owner's region, and have no methods of
        // their own to translate.
        if (Declarations.Has(type.OriginalDefinition, RegionAttribute)) return false;
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
    // R25.2. `notnull` is a nullable-analysis hint: it gives `T` no operation, so it is
    // no typeclass obligation, and a parameter carrying only it is unconstrained.
    public static bool Unconstrained(ITypeParameterSymbol tp) =>
        tp.ConstraintTypes.IsEmpty &&
        !tp.HasReferenceTypeConstraint &&
        !tp.HasValueTypeConstraint &&
        !tp.HasConstructorConstraint &&
        !tp.HasUnmanagedTypeConstraint;

    /// <summary>
    /// R27.35. A region class as the type argument of another class (<c>Stack&lt;Node&gt;</c>)
    /// is its nullable pointer: the elements are plain boxes, and <c>default</c> -- what
    /// <c>new T[n]</c> fills an array with -- is null.
    /// </summary>
    private IrType RegionArgument(ITypeSymbol argument, IrType mapped) =>
        mapped is IrClassType { Nullable: false } k && IsRegionClass(argument) ? k with { Nullable = true } : mapped;

    /// <summary>R31.2. A pair's component: a region pointer or a ring owner is the nullable pointer.</summary>
    private IrType PairComponent(ITypeSymbol argument, IrType mapped) =>
        mapped is IrClassType { Nullable: false } k && IsRingOwner(argument) ? k with { Nullable = true } : RegionArgument(argument, mapped);

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
        var all = method.ContainingType is { } rowner && IsRegionDeclaration(rowner)
            ? [.. OuterAndOwnTypeArguments(rowner), .. method.TypeArguments]
            : method.ContainingType is { TypeArguments.IsEmpty: false } owner
            ? owner.TypeArguments.AddRange(method.TypeArguments)
            : method.TypeArguments;
        if (all.IsEmpty) return ImmutableArray<IrType>.Empty;
        var classArgs = method.ContainingType is { } c && !IsRegionDeclaration(c) ? c.TypeArguments.Length : 0;
        var mapped = ImmutableArray.CreateBuilder<IrType>();
        foreach (var a in all)
        {
            if (MapType(a) is not { } t) return ImmutableArray<IrType>.Empty;
            mapped.Add(mapped.Count < classArgs ? RegionArgument(a, t) : t);
        }
        return mapped.ToImmutable();
    }

    /// <summary>R20.4. <c>List&lt;T&gt;</c>, <c>IList&lt;T&gt;</c> or <c>IReadOnlyList&lt;T&gt;</c>.</summary>
    public static bool IsListLike(ITypeSymbol? type) =>
        type is INamedTypeSymbol { TypeArguments.Length: 1 } named &&
        // R22.1. Not when the compilation declares the list: that is the list itself,
        // being verified, and it is translated as the class it is.
        !named.OriginalDefinition.Locations.Any(l => l.IsInSource) &&
        named.OriginalDefinition.ToDisplayString() is
            "System.Collections.Generic.List<T>" or
            "System.Collections.Generic.IList<T>" or
            "System.Collections.Generic.IReadOnlyList<T>";

    /// <summary>R26.8. The F* type of a value tuple <c>(T1, T2)</c>.</summary>
    public const string TupleType = "tuple2";

    /// <summary>R29.1. <c>KeyValuePair&lt;K, V&gt;</c>, which is a pair too.</summary>
    public static bool IsKeyValuePair(ITypeSymbol? type) =>
        type is INamedTypeSymbol { TypeArguments.Length: 2 } named &&
        named.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.KeyValuePair<TKey, TValue>";

    /// <summary>R29.4. <c>DictionaryEntry</c>, a pair of <c>object</c>s.</summary>
    public static bool IsDictionaryEntry(ITypeSymbol? type) =>
        type?.ToDisplayString() == "System.Collections.DictionaryEntry";

    /// <summary>R26.8/R29.1. A value tuple of two, a <c>KeyValuePair</c>, or a <c>DictionaryEntry</c>.</summary>
    public static bool IsPairType(ITypeSymbol? type) =>
        type is INamedTypeSymbol { IsTupleType: true, TupleElements.Length: 2 } || IsKeyValuePair(type) ||
        IsDictionaryEntry(type);

    /// <summary>R29.4. The F* type of an <c>object</c>: <c>Pulse.Lib.CSharp.Obj</c>'s abstract one.</summary>
    public const string ObjType = "Pulse.Lib.CSharp.Obj.obj";

    /// <summary>R29.4. The F* function that converts a value to <see cref="ObjType"/>.</summary>
    public const string BoxFunction = "Pulse.Lib.CSharp.Obj.box";

    public static readonly IrUserSpecType Obj = new("Object", ObjType, []);

    public static bool IsObj(IrType? t) => t is IrUserSpecType { FStar: ObjType };

    /// <summary>
    /// R29.4. <c>object</c>, and the enumerator interfaces a collection's explicit members
    /// return: a value of one of them is an <see cref="ObjType"/>.
    /// </summary>
    public static bool IsObjectLike(ITypeSymbol? type) =>
        type is { SpecialType: SpecialType.System_Object } ||
        type is INamedTypeSymbol { TypeKind: TypeKind.Interface } i &&
        i.OriginalDefinition.ToDisplayString() is "System.Collections.IEnumerator"
            or "System.Collections.Generic.IEnumerator<T>" or "System.Collections.IDictionaryEnumerator"
            // R35.6. And the collection interfaces a dictionary's explicit `Keys` and `Values` return.
            or "System.Collections.ICollection" or "System.Collections.Generic.ICollection<T>"
            or "System.Collections.Generic.IEnumerable<T>";

    /// <summary>R35.6. The collection interfaces <see cref="IsObjectLike"/> admits.</summary>
    public static bool IsCollectionInterface(ITypeSymbol? type) =>
        type is INamedTypeSymbol { TypeKind: TypeKind.Interface } i &&
        i.OriginalDefinition.ToDisplayString() is "System.Collections.ICollection"
            or "System.Collections.Generic.ICollection<T>" or "System.Collections.Generic.IEnumerable<T>";

    private static bool IsPlainValue(IrType t) =>
        t is IrPrim or IrTypeParamType or IrUserSpecType or IrOptionType { Inner: IrPrim or IrTypeParamType or IrUserSpecType };

    /// <summary>
    /// R26.8. The type parameters whose <c>default</c> a <c>default</c> of
    /// <paramref name="type"/> takes: the parameter itself, or a tuple's.
    /// </summary>
    public static IEnumerable<ITypeParameterSymbol> DefaultedIn(ITypeSymbol? type) =>
        type is null ? [] : ExprLowerer.TypeParametersIn(type);

    /// <summary>
    /// R26.1. The BCL delegates a collection calls: a pure function of its arguments
    /// (trusted, R26.12), so that a call and a contract can both say what it returns.
    /// </summary>
    private IrType? CallableDelegate(INamedTypeSymbol del)
    {
        if (del.ContainingNamespace?.ToDisplayString() != "System" ||
            del.MetadataName is not ("Predicate`1" or "Action`1" or "Converter`2" or "Comparison`1"))
            return null;
        if (del.DelegateInvokeMethod is not { } invoke ||
            invoke.Parameters.Any(p => p.RefKind != RefKind.None))
            return null;
        var ps = ImmutableArray.CreateBuilder<IrType>();
        foreach (var p in invoke.Parameters)
        {
            if (MapType(p.Type) is not { } pt) return null;
            ps.Add(pt);
        }
        var ret = invoke.ReturnsVoid ? new IrPulseType("unit", "unit") : MapType(invoke.ReturnType);
        if (ret is null) return null;
        return new IrDelegateType(del.ToDisplayString()) { Params = ps.ToImmutable(), Return = ret };
    }

    public IrType? MapType(ITypeSymbol? type)
    {
        switch (type)
        {
            case null:
                return null;
            case IArrayTypeSymbol { Rank: 1 } array when MapType(array.ElementType) is { } e:
                return new IrArrayType(e);
            // R20.4. `List<T>`, `IList<T>` and `IReadOnlyList<T>` are an array: an indexed
            // sequence with a length. Nothing that changes a list's size translates (each
            // is a call into the BCL, refused by R18.1), so the length is fixed for as long
            // as verified code holds the list, which is all an array is.
            case INamedTypeSymbol named when IsListLike(named) && MapType(named.TypeArguments[0]) is { } le:
                return new IrArrayType(le);
            // R20.3. `T?` on a value type is `option T`.
            case INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } nullable
                when MapType(nullable.TypeArguments[0]) is { } inner:
                return new IrOptionType(inner);
            // R20.10. The BCL value types with a pure model.
            case INamedTypeSymbol named when Bcl.MapType(named, MapType) is { } bcl:
                return bcl;
            // R26.8. A pair `(T1, T2)` of values is F*'s `T1 & T2`. A component that is an
            // object or an array would make the pair a second owner of it, so it is refused.
            // R27.43. A pointer into a region is plain data (R27.35), so it may be a component;
            // like a type argument, it is the nullable pointer, so the pair has C#'s default.
            case INamedTypeSymbol { IsTupleType: true, TupleElements.Length: 2 } tuple
                when MapType(tuple.TupleElements[0].Type) is { } t1 &&
                     (IsPlainValue(t1) || IsRegionClass(tuple.TupleElements[0].Type) || IsRingOwner(tuple.TupleElements[0].Type)) &&
                     MapType(tuple.TupleElements[1].Type) is { } t2 &&
                     (IsPlainValue(t2) || IsRegionClass(tuple.TupleElements[1].Type) || IsRingOwner(tuple.TupleElements[1].Type)):
                return new IrUserSpecType("ValueTuple", TupleType,
                    [PairComponent(tuple.TupleElements[0].Type, t1), PairComponent(tuple.TupleElements[1].Type, t2)]);
            // R29.1. `KeyValuePair<K, V>` is the same pair: a readonly struct of two values.
            case INamedTypeSymbol kvp when IsKeyValuePair(kvp) &&
                     MapType(kvp.TypeArguments[0]) is { } k && IsPlainValue(k) &&
                     MapType(kvp.TypeArguments[1]) is { } v && IsPlainValue(v):
                return new IrUserSpecType("ValueTuple", TupleType, [k, v]);
            // R29.4. `object` and the enumerator interfaces are F*'s abstract `obj`, and a
            // `DictionaryEntry` is a pair of them.
            case { } o when IsObjectLike(o):
                return Obj;
            case { } de when IsDictionaryEntry(de):
                return new IrUserSpecType("ValueTuple", TupleType, [Obj, Obj]);
            // R20.3. A delegate is held, passed on, and nothing else.
            case INamedTypeSymbol { TypeKind: TypeKind.Delegate } del when CallableDelegate(del) is { } callable:
                return callable;
            case INamedTypeSymbol { TypeKind: TypeKind.Delegate } del:
                return new IrDelegateType(del.ToDisplayString());
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
            // R27.35. A sequence of region pointers is a sequence of nullable boxes, as the
            // model of a `Stack<Node>` is.
            case INamedTypeSymbol named when IsSeq(named) && MapType(named.TypeArguments[0]) is { } se:
                return new IrSeqType(RegionArgument(named.TypeArguments[0], se));
            case INamedTypeSymbol named when IsGhost(named) && MapType(named.TypeArguments[0]) is { } ge:
                return new IrGhostType(ge);
            case INamedTypeSymbol named when IsSpecList(named) && MapType(named.TypeArguments[0]) is { } le:
                return new IrSpecListType(le);
            // R11.1. A user-declared specification type. It is tried before the class
            // rule because a `[SpecType]` may be a class, and before the struct rule
            // because it is usually a struct — it is not a representation either way.
            // R19.1. Before the class rule: an exception is a value of F*'s `exn`.
            case INamedTypeSymbol named when IsSystemException(named):
                return new IrExnType(null);
            case INamedTypeSymbol named when IsExceptionClass(named):
                return new IrExnType(named.Name);
            case INamedTypeSymbol named when IsLibraryException(named):
                return new IrExnType(null);
            case INamedTypeSymbol named when SpecTypeName(named) is { } fstar:
            {
                var args = ImmutableArray.CreateBuilder<IrType>();
                // R27.58. A bound class nested in a generic class is applied to the type
                // arguments of the classes it is nested in, then its own (R24.6).
                var applied = Binding(named) is not null
                    ? AllTypeArguments(named)
                    : named.TypeArguments;
                foreach (var a in applied)
                {
                    if (MapType(a) is not { } mapped) return null;
                    args.Add(mapped);
                }
                var spec = new IrUserSpecType((CaseBase(named) ?? named).Name, fstar, args.ToImmutable());
                // R20.11. A nullable specification type is an `option` of its F* type,
                // except where `#nullable enable` says this occurrence is not null.
                return IsNullableSpecType(named) &&
                       named.NullableAnnotation != NullableAnnotation.NotAnnotated
                    ? new IrOptionType(spec)
                    : spec;
            }
            // §3.4. A class is translated exactly when it declares a [Model] member: R3.9
            // makes the model mandatory, so its presence is the same test as "annotated".
            // R10.2. `C?` is the nullable pointer and `C` is its non-null refinement, and
            // the annotation is part of the type: it is what makes the base case of R10.3's
            // induction reachable by the prover.
            // R12.1. A `[Plain]` class is translated too, and is translated for the same
            // reason: it has a representation. What it does not have is a model, so it is
            // recognised by the attribute rather than by the `[Model]` member.
            // R29.3. A class that borrows its owner is the record of its fields.
            case INamedTypeSymbol { TypeKind: TypeKind.Class } borrowing when Borrowing.IsBorrowingClass(borrowing, this):
                return NamedStruct(borrowing);
            // R27.57. A representation-sharing subclass is its base's type.
            case INamedTypeSymbol { TypeKind: TypeKind.Class } alias when Subclasses.AliasBase(alias, this) is { } aliased:
                return MapType(aliased) is IrClassType ak
                    ? ak with { Nullable = alias.NullableAnnotation == NullableAnnotation.Annotated }
                    : null;
            case INamedTypeSymbol { TypeKind: TypeKind.Class } named
                when HasModel(named) || IsPlainLike(named.OriginalDefinition):
            {
                // R15.3. A constructed generic class carries its resolved arguments. An
                // argument this cannot map makes the whole type unmappable, so the
                // refusal lands on the class type rather than silently dropping a
                // parameter and emitting a term with a free variable in it.
                var classArgs = ImmutableArray.CreateBuilder<IrType>();
                foreach (var a in Declarations.Has(named.OriginalDefinition, RegionAttribute)
                             ? OuterAndOwnTypeArguments(named) : named.TypeArguments)
                {
                    if (MapType(a) is not { } mapped) return null;
                    // R27.35. A region class as the argument of another class (`Stack<Node>`)
                    // is its nullable pointer: the elements are plain boxes, and `default` --
                    // what `new T[n]` fills an array with -- is null.
                    classArgs.Add(Declarations.Has(named.OriginalDefinition, RegionAttribute) ? mapped : RegionArgument(a, mapped));
                }
                return new IrClassType(named.Name, named.NullableAnnotation == NullableAnnotation.Annotated)
                {
                    Plain = IsPlainLike(named.OriginalDefinition),
                    TypeArguments = classArgs.ToImmutable(),
                };
            }
        }

        // R22.2. An enum without a `[SpecType]` is its underlying integer type, as its
        // constants already are (R20.9): a tag passed along, compared, never matched on.
        if (type is INamedTypeSymbol { TypeKind: TypeKind.Enum, EnumUnderlyingType: { } underlying })
            return MapType(underlying);

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
            SpecialType.System_Decimal => new IrPrim(PrimKind.Decimal),
            // R20.9. A `string` declared where nullable reference types are disabled is
            // *oblivious*: C# lets it be null, and the program may test it. It is an
            // `option string`. A `string` under `#nullable enable` stays non-null.
            SpecialType.System_String => obliviousStrings &&
                                          type.NullableAnnotation == NullableAnnotation.None
                ? new IrOptionType(new IrPrim(PrimKind.String))
                : new IrPrim(PrimKind.String),
            _ => type.TypeKind == TypeKind.Struct ? NamedStruct(type) : null,
        };
    }

    /// <summary>R3.4, and R22.6 for a generic <c>[Spec]</c> struct.</summary>
    private IrNamedType? NamedStruct(ITypeSymbol type)
    {
        if (type is not INamedTypeSymbol named) return new IrNamedType(type.Name);
        var all = AllTypeArguments(named);
        if (all.IsEmpty) return new IrNamedType(StructName(named));
        var args = ImmutableArray.CreateBuilder<IrType>();
        foreach (var a in all)
        {
            if (MapType(a) is not { } mapped) return null;
            args.Add(mapped);
        }
        return new IrNamedType(StructName(named)) { TypeArguments = args.ToImmutable() };
    }

    /// <summary>
    /// R24.6. A struct nested in a generic type (`HashSet&lt;T&gt;.Entry`) is implicitly
    /// generic in the outer parameters, so they lead its own; and two such structs may
    /// share a simple name (`HashSet&lt;T&gt;.Entry`, `Dictionary&lt;K,V&gt;.Entry`), so its
    /// name is qualified by the outer type's. A class between the struct and the generic type
    /// (`PriorityQueue&lt;E, P&gt;.UnorderedItemsCollection.Enumerator`, R28) passes the
    /// outer parameters through, after adding its own.
    /// </summary>
    public static ImmutableArray<ITypeSymbol> AllTypeArguments(INamedTypeSymbol named) =>
        named.ContainingType is { } outer && OuterGeneric(named)
            ? [.. EnclosingArguments(outer), .. named.TypeArguments]
            : named.TypeArguments;

    public static ImmutableArray<ITypeParameterSymbol> AllTypeParameters(INamedTypeSymbol named) =>
        named.ContainingType is { } outer && OuterGeneric(named)
            ? [.. EnclosingParameters(outer), .. named.TypeParameters]
            : named.TypeParameters;

    private static ImmutableArray<ITypeSymbol> EnclosingArguments(INamedTypeSymbol t) =>
        t.ContainingType is { } o ? [.. EnclosingArguments(o), .. t.TypeArguments] : t.TypeArguments;

    private static ImmutableArray<ITypeParameterSymbol> EnclosingParameters(INamedTypeSymbol t) =>
        t.ContainingType is { } o ? [.. EnclosingParameters(o), .. t.TypeParameters] : t.TypeParameters;

    public static string StructName(INamedTypeSymbol named) =>
        named.ContainingType is { } outer && OuterGeneric(named)
            ? $"{outer.Name}_{named.Name}"
            : named.Name;

    private static bool OuterGeneric(INamedTypeSymbol named) =>
        named.TypeKind is TypeKind.Struct or TypeKind.Class &&
        named.ContainingType is { } outer && (outer.IsGenericType || OuterGeneric(outer));
}
