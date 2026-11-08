using System.Collections.Immutable;
using System.Text;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// R2.2. The C# a generated top-level construct came from. <c>Construct</c> is the
/// emitted F* name, or <c>"*"</c> for a module whose whole text is the user's own Pulse.
/// </summary>
public sealed record Provenance(string Construct, IrLoc Loc);

/// <summary>One line of a generated module, and the C# it was emitted for.</summary>
public readonly record struct EmittedLine(string Text, IrLoc? Loc);

/// <summary>
/// A one-based line of a generated module, and the C# it came from. This is the map an
/// F* error is read through: F* reports a range in a `.fst` nobody wrote, and the only
/// thing that knows what that line was *for* is the emitter that produced it.
/// </summary>
public sealed record LineOrigin(int Line, IrLoc Source);

/// <summary>A generated Pulse module.</summary>
public sealed record EmittedModule(string Name, string Text)
{
    public string FileName => Name + ".fst";

    /// <summary>
    /// R9.17. The module's interface, when it has one. A class whose encoding a client has
    /// no business seeing publishes what a client may use and keeps the rest to itself;
    /// F* then checks the implementation against it, so the separation is enforced rather
    /// than merely intended.
    /// </summary>
    public string? Interface { get; init; }

    public string InterfaceFileName => Name + ".fsti";

    /// <summary>
    /// R2.2. What this module declares and where each declaration came from. A construct
    /// absent from here was invented by the emitter, which the provenance lint reports:
    /// anything the translator produces that no C# asked for has to be justified as a
    /// numbered rule in doc/translation.md.
    /// </summary>
    public ImmutableArray<Provenance> Origin { get; init; } = ImmutableArray<Provenance>.Empty;

    /// <summary>
    /// Where in this module each piece of C# ended up, ascending by line. Coarse by
    /// design: a statement, a clause of a contract, a declaration. Finer would be a
    /// promise the emitter cannot keep, because one C# statement routinely becomes
    /// several Pulse ones and the interesting failures are about the ones in between.
    /// </summary>
    public ImmutableArray<LineOrigin> Origins { get; init; } = ImmutableArray<LineOrigin>.Empty;
}

/// <summary>
/// How a C# name is represented in the emitted Pulse: as an immutable binder, as a
/// mutable <c>ref</c> cell, or as a live array with a ghost contents binder.
/// </summary>
public sealed record Slot(string Name, IrType Type, SlotKind Kind, string Binder)
{
    /// <summary>
    /// The permission variable introduced by <c>[Frac("p")]</c>, if any. A slot that has
    /// one is read-only: it can be observed but not written, here or by a callee.
    /// </summary>
    public string? Fraction { get; init; }

    /// <summary>
    /// The permission this slot's resources are held at, ready to splice in front of a
    /// value binder: <c>"#p "</c>, or empty for full ownership. R3.10c makes a class
    /// invariant carry one too, so an object slot renders it exactly as an array does.
    /// </summary>
    public string PermArg => Perm;

    private string Perm => Fraction is null ? "" : $"#{Fraction} ";

    /// <summary>
    /// R27.13. For a receiver held at <c>class_C__inv_heap</c>: each region it owns, with
    /// the ghost binders naming its heap on entry and on exit. Empty for the plain invariant.
    /// </summary>
    public ImmutableArray<(IrClassType Region, string Pre, string Post)> Heaps { get; init; } = [];

    /// <summary>For an object slot: the ghost binder holding its model on entry.</summary>
    public string? PreModel { get; init; }

    /// <summary>
    /// For an object slot: the binder its invariant is re-folded at on exit. Equal to
    /// <see cref="PreModel"/> for a read-only method (R4.11a).
    /// </summary>
    public string? PostModel { get; init; }

    /// <summary>
    /// R9.14. For an <c>override</c>'s receiver: the base class whose model its inherited
    /// contract is written at. The slot is then owned through <c>class_C__as_B</c>, and its
    /// <see cref="PreModel"/> holds a model of <em>B</em>; the method's own fields are
    /// reached by opening that view, which is what <see cref="OwnModel"/> names.
    /// </summary>
    public string? ViewBase { get; init; }

    /// <summary>
    /// R4.9c. True when the caller gave this object away: the method's postcondition owns
    /// nothing of it, and R10.7's null case must therefore consume rather than preserve.
    /// </summary>
    public bool Consumed { get; init; }

    /// <summary>
    /// R10.7. True inside the <c>else</c> branch of a null test on this reference, where
    /// the head cell has been given up by <c>elim_cons</c>. The slot's type stays nullable
    /// — the reference is still an <c>option</c>, and passing it on or returning it is
    /// unchanged — but the representation behind it is now reachable, which is the only
    /// thing the window adds.
    /// </summary>
    public bool Window { get; init; }

    /// <summary>
    /// R24.7. For a local array: it was initialised from a nullable array field, so the
    /// array it holds is owned through <c>NA.pts_to</c> rather than <c>A.pts_to</c>.
    /// </summary>
    public bool NullableArray { get; init; }

    /// <summary>R27.23. The receiver of an <c>[Open]</c> method: held as its record and heaps.</summary>
    /// <summary>R27.23. An <c>[Open]</c> receiver's fields and regions, for ghost statements.</summary>
    public ImmutableArray<IrFieldDecl> OpenFields { get; init; } = [];
    public ImmutableArray<IrClassType> OpenHeaps { get; init; } = [];

    public bool Open { get; init; }

    /// <summary>R27.41. For a folded receiver held at its heaps: the heap values a loop names.</summary>
    public ImmutableArray<string> LoopHeaps { get; init; }

    /// <summary>R10.7. The reference, as a non-null one. Legal only in a window.</summary>
    // R10.2 (F76). A nullable reference and a non-nullable one are the same term: the
    // non-nullable type is the nullable one under a refinement, so "the non-null form of
    // this slot" is the slot. Kept as a name because the *concept* still exists — a
    // position that requires non-nullness — even though extracting it now costs nothing.
    public string NonNull => Binder;

    /// <summary>R9.14. The binder for this class's own model inside an <c>override</c>.</summary>
    public string OwnModel => "own_" + Name;

    /// <summary>
    /// R9.16. For a hierarchy-typed slot whose object record is known: the term naming it.
    /// A slot that has one is owned through <c>class_C__inv_at</c> rather than the plain
    /// invariant, which is what makes a checked downcast writable — and it is the only
    /// difference, because R9.10 emits every dispatching wrapper at the index too.
    /// </summary>
    public string? Index { get; init; }

    /// <summary>
    /// R9.18. For a reference upcast from an *intermediate* class: the object record one
    /// level down — the index the source was held at. <see cref="Index"/> is that record
    /// seen as the base's, and the two are related by the view, so a cast back to the
    /// intermediate class recovers this one. Null for a reference whose dynamic type is a
    /// direct subclass of its static one, where the two coincide.
    /// </summary>
    public string? Sub { get; init; }

    /// <summary>
    /// R9.16. The class this reference was cast to. C# leaves the base name usable after
    /// a cast; the encoding does not, because the cast <em>moved</em> the invariant onto
    /// the derived reference. A later mention is reported against the C#.
    /// </summary>
    public string? Cast { get; init; }

    /// <summary>R4.9c, R4.12b. The callee this reference's invariant was handed to.</summary>
    public string? Given { get; init; }

    /// <summary>
    /// R17.6. How a span local was borrowed, and so which receipt <c>Pal.Restore</c>
    /// redeems. Null on a span *parameter*, which carries no receipt: the caller borrowed
    /// it and the caller gives it back.
    /// </summary>
    public SpanOrigin? Origin { get; init; }

    /// <summary>The resource conjunct owning this slot, given a value binder.</summary>
    public string Resource(string value) => Kind switch
    {
        SlotKind.Cell => $"R.pts_to {Binder} {value}",
        SlotKind.RefParam => $"R.pts_to {Binder} {Perm}{value}",
        SlotKind.Array => $"A.pts_to {Binder} {Perm}{value}",
        SlotKind.Span => $"S.pts_to {Binder} {Perm}{value}",
        // R27.23. An `[Open]` receiver is held as its record.
        SlotKind.Object when Open => $"B.pts_to {Binder} {value}",
        // R27.41. A receiver held at its heaps and not opened, carried across a loop at
        // the heap values the loop names.
        SlotKind.Object when Type is IrClassType c && !LoopHeaps.IsDefaultOrEmpty =>
            $"{Names.ClassModule(c.Name)}.{Names.ClassInvHeap(c.Name)} {Binder} {Perm}{value} {string.Join(" ", LoopHeaps)}",
        SlotKind.Object when Type is IrClassType c && Index is not null =>
            $"{Names.ClassModule(c.Name)}.{Names.ClassInvAt(c.Name)} {Binder} {Index} " +
            $"{(Fraction ?? "1.0R")} {value}",
        SlotKind.Object when Type is IrClassType c =>
            $"{Names.ClassModule(c.Name)}.{Names.ClassInv(c.Name)} {Binder} {Perm}{value}",
        // R27.39. A callback's trace is owned through its protocol.
        SlotKind.Trace => $"{Binder} {value}",
        _ => "",
    };

    public bool Owns => Kind is SlotKind.Cell or SlotKind.RefParam or SlotKind.Array
        or SlotKind.Span or SlotKind.Object or SlotKind.Trace;
}

public enum SlotKind
{
    /// <summary>An immutable by-value parameter; no resource.</summary>
    Value,
    /// <summary>A local, or a by-value parameter the body assigns (R5.2, R4.2).</summary>
    Cell,
    /// <summary>A <c>ref</c>/<c>out</c>/<c>in</c> parameter.</summary>
    RefParam,
    /// <summary>An array parameter.</summary>
    Array,
    /// <summary>R17.1. A span: a borrowed window, owned through <c>Slice.pts_to</c>.</summary>
    Span,
    /// <summary>
    /// An object: a <c>B.box</c> of the class's representation, owned through
    /// <c>class_C__inv</c> rather than a <c>pts_to</c> (R3.8, R4.10).
    /// </summary>
    Object,
    /// <summary>
    /// R27.39. The trace of a <c>[Callback]</c> parameter, owned through the protocol the
    /// caller passed with it.
    /// </summary>
    Trace,
}

/// <summary>
/// The Emit stage: one Pulse module per C# declaration, following
/// <c>doc/translation.md</c>. The emitter contributes no proof steps of its own
/// (§0 rule 3); everything it writes is either the user's code, the user's
/// annotations, or a call into <c>Pulse.Lib.CSharp.*</c>.
/// </summary>
public sealed class PulseEmitter(DiagnosticBag diagnostics)
{
    private readonly SpecEmitter _spec = new(diagnostics);
    private Dictionary<string, IrClass> _classes = [];
    private readonly HierarchyEmitter _hierarchy = new(new SpecEmitter(diagnostics), diagnostics);
    private readonly RecursiveEmitter _recursive =
        new(new SpecEmitter(diagnostics), new HierarchyEmitter(new SpecEmitter(diagnostics), diagnostics));

    /// <summary>
    /// R9.7. For each <c>override</c>, the class whose model its contract is written at.
    /// The body of an override is typed against <c>class_C__as_B</c> rather than
    /// <c>class_C__inv</c> (see <c>MethodPlan</c>), so a caller naming it directly — which
    /// is what a call at the leaf's own static type is — has to present the receiver the
    /// same way.
    /// </summary>
    private Dictionary<string, string> _overrides = [];

    /// <summary>R10.6. Whether the method being emitted calls itself; see Dependencies.</summary>
    private bool _recursiveMethod;

    /// <summary>
    /// R9.12. The names of the <c>abstract</c> methods — the vtable slots. A call is
    /// virtual exactly when it resolves to one of these: a <em>concrete</em> method of an
    /// abstract class (R9.13) has a body, a <c>Func_</c> module and no slot, so it is
    /// called directly even though its receiver is abstractly typed.
    /// </summary>
    private HashSet<string> _slots = [];

    /// <summary>R4.9c, R4.12b. The argument positions each method takes ownership at.</summary>
    private Dictionary<string, ImmutableHashSet<int>> _consumed = [];
    private Dictionary<string, IrMethod> _methods = [];

    /// <summary>
    /// R27.13. The methods whose contract speaks of their receiver's regions, each with the
    /// region classes its receiver is held at the heaps of.
    /// </summary>
    private Dictionary<string, ImmutableArray<IrClassType>> _heapIndexed = [];
    private HashSet<string> _openMethods = [];

    /// <summary>R27.50. The owner classes two references of which some method compares.</summary>
    private HashSet<string> _compared = [];

    /// <summary>R27.50. The methods R4.11 found read-only.</summary>
    private HashSet<string> _readOnly = [];

    /// <summary>
    /// R27.50. The owner classes (not region classes) two non-null references of which the
    /// method's body compares with <c>==</c> or <c>!=</c>.
    /// </summary>
    internal static IEnumerable<string> ComparedClasses(IrMethod method, IReadOnlyDictionary<string, IrClass> classes) =>
        method.Body is null ? []
        : Pal.Compiler.Passes.Check.Statements(method.Body)
            .SelectMany(Pal.Compiler.Passes.Check.Expressions)
            .SelectMany(Pal.Compiler.Passes.Check.Subexpressions)
            .OfType<IrBinary>()
            .Where(b => b.Op is BinOp.Eq or BinOp.Ne &&
                        b.Left.Type is IrClassType { Nullable: false } l &&
                        b.Right.Type is IrClassType { Nullable: false } r && l.Name == r.Name &&
                        classes.TryGetValue(l.Name, out var d) && !d.IsRegion)
            .Select(b => ((IrClassType)b.Left.Type!).Name)
            .Distinct();

    /// <summary>§9. The <c>abstract</c> methods of each abstract class: its vtable slots.</summary>
    private ILookup<string, IrMethod> _virtuals =
        Enumerable.Empty<IrMethod>().ToLookup(m => "", m => m);

    public ImmutableArray<EmittedModule> Emit(IrProgram program)
    {
        var modules = ImmutableArray.CreateBuilder<EmittedModule>();
        _classes = program.Declarations.OfType<IrClass>()
            .GroupBy(c => c.Name).ToDictionary(g => g.Key, g => g.First());
        // R9.19. Both spec emitters need the base chain, to compose R9.6's forgetting when
        // an observation is read off a model further down the hierarchy than it was
        // declared. There is one hierarchy per program, so it is computed once.
        var bases = _classes.Values
            .Where(c => c.BaseClass is not null)
            .GroupBy(c => c.Name)
            .ToDictionary(g => g.Key, g => g.First().BaseClass!);
        _spec.Bases = bases;
        _hierarchy.Bases = bases;
        _virtuals = program.Declarations.OfType<IrMethod>()
            .Where(m => m is { IsAbstract: true, DeclaringClass: not null })
            .ToLookup(m => m.DeclaringClass!);
        _slots = [.. program.Declarations.OfType<IrMethod>()
            .Where(m => m.IsAbstract).Select(m => m.Name)];
        // R18.3. Two declarations may not compete for one name, and the frontend refuses
        // the way that happens today (two constructors, PALCS0501). These lookups are keyed
        // by name, so a collision that slipped through would abort the process inside
        // `ToDictionary` — no diagnostic, no output, a stack trace naming a dictionary.
        // Grouping instead means a frontend refusal is what the user sees.
        _overrides = program.Declarations.OfType<IrMethod>()
            .Where(m => m.Overrides is not null)
            .GroupBy(m => m.Name)
            .ToDictionary(g => g.Key, g => g.First().Overrides!);
        // R4.9c, R4.12b, on the calling side. Which of a callee's parameters take their
        // argument's invariant with them, by position, so that a call site can stop owning
        // what it handed over. Computed from the same predicate the callee's own contract
        // is built from, once, because it is a property of the program and not of a call.
        _methods = program.Declarations.OfType<IrMethod>()
            .GroupBy(m => m.Name)
            .ToDictionary(g => g.Key, g => g.First());
        _consumed = program.Declarations.OfType<IrMethod>()
            .GroupBy(m => m.Name)
            .ToDictionary(
                g => g.Key,
                g => Enumerable.Range(0, g.First().Parameters.Length)
                    .Where(i => MethodPlan.Consumed(g.First(), g.First().Parameters[i], _methods))
                    .ToImmutableHashSet());
        _heapsKept = HeapsKept(program.Declarations.OfType<IrMethod>().ToImmutableArray());
        _heapIndexed = program.Declarations.OfType<IrMethod>()
            .Select(m => (m, HeapRegions(m)))
            .Where(x => !x.Item2.IsEmpty)
            .GroupBy(x => x.m.Name)
            .ToDictionary(g => g.Key, g => g.First().Item2);
        _openMethods = new HashSet<string>(program.Declarations.OfType<IrMethod>().Where(m => m.Open).Select(m => m.Name));
        _readOnly = [.. program.Declarations.OfType<IrMethod>().Where(m => m.IsReadOnly).Select(m => m.Name)];
        _compared = [.. program.Declarations.OfType<IrMethod>().SelectMany(m => ComparedClasses(m, _classes))];
        _regionHeld = RegionHeld(program.Declarations.OfType<IrMethod>().ToImmutableArray());
        _raising = new HashSet<string>(program.Declarations.OfType<IrMethod>().Where(m => !m.Throws.IsEmpty).Select(m => m.Name));
        // R27.38. A call to an owner's method that gives its heaps back writes no region.
        foreach (var kept in _heapsKept)
            if (!_regionHeld.ContainsKey(kept)) _regionHeld[kept] = [];
        _ownedFields = program.Declarations.OfType<IrStruct>()
            .Where(st => st.Fields.Any(f => f.IsOwned))
            .GroupBy(st => st.Name)
            .ToDictionary(g => g.Key, g => g.First().Fields.Where(f => f.IsOwned).ToImmutableArray());
        var exceptions = program.Declarations.OfType<IrException>().ToImmutableArray();
        if (!exceptions.IsEmpty) modules.Add(EmitExceptions(exceptions));

        foreach (var decl in program.Declarations)
        {
            var module = decl switch
            {
                IrSpecFunction s => EmitSpecFunction(s),
                // R9.9. An abstract method is a vtable slot, and the slot is emitted with
                // the vtable. There is no module of its own to emit, and no body to check.
                IrMethod { IsAbstract: true } => null,
                IrMethod { IsLemma: true } m => EmitLemma(m),
                IrMethod m => EmitMethod(m),
                IrStruct s => EmitStruct(s),
                IrClass { IsAbstract: true } c => EmitAbstractClass(c),
                IrClass c => EmitClass(c),
                IrIncludePulse i => new EmittedModule(i.Module, i.Text),
                _ => null,
            };
            if (module is null) continue;

            var construct = decl switch
            {
                IrSpecFunction s => Names.SpecFunction(s.Name),
                IrMethod { IsLemma: true } m => Names.Lemma(m.Name),
                IrMethod m => Names.Function(m.Name),
                IrStruct s => Names.StructType(s.Name),
                IrClass c => Names.ClassType(c.Name),
                _ => "*",
            };

            // R3.4 emits three constructs for one C# declaration — the record, its
            // refinement predicate, and the refined type — so all three are recorded
            // against the same span rather than leaving two of them unaccounted for.
            ImmutableArray<Provenance> origin = decl switch
            {
                IrStruct st =>
                [
                    new Provenance(Names.StructRaw(st.Name), decl.Loc),
                    new Provenance(Names.StructPred(st.Name), decl.Loc),
                    new Provenance(Names.StructType(st.Name), decl.Loc),
                ],
                // §3.4 emits five constructs plus one per [Spec] member for a single C#
                // class declaration, so each is recorded against the span it came from
                // rather than leaving five of them unaccounted for.
                // §9. An abstract class has no representation: it emits a vtable, the dyn
                // its references are, and the two invariants. R9.11's share and gather are
                // dispatched rather than proved, and each virtual method contributes the
                // slot and its two dispatching wrappers.
                IrClass { IsAbstract: true } ab =>
                [
                    new Provenance(Names.ClassModelPred(ab.Name), decl.Loc),
                    new Provenance(Names.ClassModel(ab.Name), decl.Loc),
                    new Provenance(Names.ClassVtbl(ab.Name), decl.Loc),
                    new Provenance(Names.ClassObj(ab.Name), decl.Loc),
                    new Provenance(Names.ClassType(ab.Name), decl.Loc),
                    new Provenance(Names.ClassAt(ab.Name), decl.Loc),
                    new Provenance(Names.ClassInv(ab.Name), decl.Loc),
                    new Provenance(Names.ClassInvAt(ab.Name), decl.Loc),
                    new Provenance(Names.ClassForgetImpl(ab.Name), decl.Loc),
                    new Provenance(Names.ClassBox(ab.Name), decl.Loc),
                    new Provenance(Names.ClassIs(ab.Name), decl.Loc),
                    new Provenance(Names.ClassRef(ab.Name), decl.Loc),
                    new Provenance(Names.ClassObjAt(ab.Name), decl.Loc),
                    new Provenance(Names.ClassIntroAt(ab.Name), decl.Loc),
                    new Provenance(Names.ClassElimAt(ab.Name), decl.Loc),
                    new Provenance(Names.ClassPack(ab.Name), decl.Loc),
                    new Provenance(Names.ClassUnpack(ab.Name), decl.Loc),
                    new Provenance(Names.ClassInvShare(ab.Name) + "_at", decl.Loc),
                    new Provenance(Names.ClassInvShare(ab.Name), decl.Loc),
                    new Provenance(Names.ClassInvGather(ab.Name) + "_at", decl.Loc),
                    .. Visible(ab).SelectMany(v => new[]
                    {
                        new Provenance(Names.DispatchAt(ab.Name, Names.Member(v.Name, v.DeclaringClass!)), v.Loc),
                        new Provenance(Names.Dispatch(ab.Name, Names.Member(v.Name, v.DeclaringClass!)), v.Loc),
                    }),
                    .. ab.Observations.Select(o =>
                        new Provenance(Names.Observation(ab.Name, o.Name), o.Loc)),
                    // R9.18. An intermediate class adds the derived vtable that presents it
                    // as its parent, and the two casts across that one edge.
                    .. ab.BaseClass is not { } sup ? ImmutableArray<Provenance>.Empty :
                    [
                        new Provenance(Names.ClassForget(ab.Name), decl.Loc),
                        new Provenance(Names.ClassAsBase(ab.Name, sup), decl.Loc),
                        new Provenance(Names.ClassBasePkg(ab.Name, sup), decl.Loc),
                        new Provenance(Names.ClassView(ab.Name), decl.Loc),
                        new Provenance(Names.ClassPkgSlot(ab.Name, "share"), decl.Loc),
                        new Provenance(Names.ClassPkgSlot(ab.Name, "gather"), decl.Loc),
                        new Provenance(Names.UpcastToAt(ab.Name, sup), decl.Loc),
                        new Provenance(Names.UpcastTo(ab.Name, sup), decl.Loc),
                        new Provenance(Names.DowncastFrom(ab.Name, sup), decl.Loc),
                        .. Visible(_classes[sup]).Select(v =>
                            new Provenance(
                                Names.ClassPkgSlot(ab.Name, Names.Member(v.Name, v.DeclaringClass!)), v.Loc)),
                    ],
                ],
                IrClass cl =>
                [
                    new Provenance(Names.ClassRaw(cl.Name), decl.Loc),
                    new Provenance(Names.ClassType(cl.Name), decl.Loc),
                    new Provenance(Names.ClassModelPred(cl.Name), decl.Loc),
                    new Provenance(Names.ClassModel(cl.Name), decl.Loc),
                    new Provenance(Names.ClassInv(cl.Name), decl.Loc),
                    // R3.10d's three lemmas. Their span is the class declaration: they
                    // exist because the class does, and there is nothing else in the C#
                    // for them to point at.
                    new Provenance(Names.ClassInvShare(cl.Name), decl.Loc),
                    new Provenance(Names.ClassInvGatherGen(cl.Name), decl.Loc),
                    new Provenance(Names.ClassInvGather(cl.Name), decl.Loc),
                    // R27.13. An owner's invariant at named heaps, and the two conversions.
                    new Provenance(Names.ClassInvHeap(cl.Name), decl.Loc),
                    new Provenance(Names.ClassToHeap(cl.Name), decl.Loc),
                    new Provenance(Names.ClassOfHeap(cl.Name), decl.Loc),
                    // R27.52. The abstraction split into representation and model.
                    new Provenance(Names.ClassAbsRep(cl.Name), decl.Loc),
                    new Provenance(Names.ClassAbsModel(cl.Name), decl.Loc),
                    // R27.38. The pure half of the invariant, for a class with no array or
                    // object field.
                    new Provenance(Names.ClassAbs(cl.Name), decl.Loc),
                    // R27.50. Two whole owners of the class are distinct.
                    new Provenance(Names.ClassDistinct(cl.Name), decl.Loc),
                    .. cl.Observations.Select(o =>
                        new Provenance(Names.Observation(cl.Name, o.Name), o.Loc)),
                    // §10. A recursive class states its invariant at the option (R10.3) and
                    // supplies the lemmas that take it apart (R10.4). Each exists because
                    // the class is recursive and points at the class declaration, which is
                    // the only C# there is for them to point at.
                    .. cl.Recursion is null ? ImmutableArray<Provenance>.Empty :
                    [
                        new Provenance(Names.ClassInvOpt(cl.Name), decl.Loc),
                        new Provenance(Names.ClassCases(cl.Name), decl.Loc),
                        new Provenance(Names.ClassNilCase(cl.Name), decl.Loc),
                        new Provenance(Names.ClassElimNil(cl.Name), decl.Loc),
                        new Provenance(Names.ClassIntroNil(cl.Name), decl.Loc),
                        new Provenance(Names.ClassElimCons(cl.Name), decl.Loc),
                        new Provenance(Names.ClassIntroCons(cl.Name), decl.Loc),
                        new Provenance(Names.ClassIntro(cl.Name), decl.Loc),
                        new Provenance(Names.ClassAsOpt(cl.Name), decl.Loc),
                        new Provenance(Names.ClassInvOptShare(cl.Name), decl.Loc),
                        new Provenance(Names.ClassInvOptGather(cl.Name), decl.Loc),
                    ],
                    // R27.3. A `[Region]` class adds its children, its view, the tree and
                    // well-formedness over a heap, and the read that knows both.
                    .. !cl.IsRegion ? ImmutableArray<Provenance>.Empty :
                    [
                        new Provenance(Frontend.Region.LeftOf(cl.Name), decl.Loc),
                        new Provenance(Frontend.Region.RightOf(cl.Name), decl.Loc),
                        new Provenance(Frontend.Region.ViewOf(cl.Name), decl.Loc),
                        new Provenance(Frontend.Region.TreeOf(cl.Name), decl.Loc),
                        new Provenance(Frontend.Region.WfOf(cl.Name), decl.Loc),
                        new Provenance(Frontend.Region.ReadOf(cl.Name), decl.Loc),
                        new Provenance(Frontend.Region.UnsharedOf(cl.Name), decl.Loc),
                        new Provenance(Frontend.Region.ReshapedOf(cl.Name), decl.Loc),
                    ],
                    // R9.14. A leaf adds the forgetting function R9.6 read off its
                    // `[Model]` override, its own invariant at the base's model, and the
                    // two lemmas that lift R3.10d's sharing to that model.
                    .. cl.BaseClass is null ? ImmutableArray<Provenance>.Empty :
                    [
                        new Provenance(Names.ClassForget(cl.Name), decl.Loc),
                        new Provenance(Names.ClassAsBase(cl.Name, cl.BaseClass), decl.Loc),
                        new Provenance(Names.ClassAsBase(cl.Name, cl.BaseClass) + "_share", decl.Loc),
                        new Provenance(Names.ClassAsBase(cl.Name, cl.BaseClass) + "_gather", decl.Loc),
                    ],
                ],
                // R27.39. A lifted lambda adds its protocol and its callback, both from the lambda.
                IrMethod { Lambda: not null } lm =>
                [
                    new Provenance(construct, decl.Loc),
                    new Provenance(Names.LambdaProtocol(lm.Name), decl.Loc),
                    new Provenance(Names.LambdaCallback(lm.Name), decl.Loc),
                ],
                _ => [new Provenance(construct, decl.Loc)],
            };

            modules.Add(module with { Origin = origin });

            // R9.14. The vtable *value* is a module of its own: it mentions every method
            // module of the leaf, and the leaf's constructor mentions it, so it has to sit
            // between them. F* computes the order from the dependencies, so nothing else
            // has to know that.
            if (decl is IrClass { IsAbstract: false, BaseClass: { } baseName } leaf &&
                _classes.TryGetValue(baseName, out var super))
            {
                var overrides = program.Declarations.OfType<IrMethod>()
                    .Where(m => m.DeclaringClass == leaf.Name && m.Overrides is not null)
                    .ToImmutableArray();
                var vtbl = _hierarchy.EmitVtbl(leaf, super, Visible(super), overrides);
                modules.Add(new EmittedModule(Names.VtblModule(leaf.Name), vtbl.Impl)
                {
                    Interface = vtbl.Iface,
                    Origin =
                    [
                        new Provenance(Names.ClassVtblValue(leaf.Name), decl.Loc),
                        new Provenance(Names.ClassObjOf(leaf.Name), decl.Loc),
                        new Provenance(Names.UpcastToAt(leaf.Name, baseName), decl.Loc),
                        new Provenance(Names.DowncastFrom(leaf.Name, baseName), decl.Loc),
                    ],
                });
            }
        }
        return modules.ToImmutable();
    }

    /// <summary>
    /// §9. An abstract class: a vtable, a dyn, and dispatch — published as an interface
    /// (R9.17) that says everything a subclass or a client may use and nothing about how a
    /// reference is represented.
    /// </summary>
    private EmittedModule EmitAbstractClass(IrClass c)
    {
        var parent = c.BaseClass is { } b && _classes.TryGetValue(b, out var super) ? super : null;
        var (iface, impl) = _hierarchy.EmitAbstract(
            c, parent, parent is null ? [] : Visible(parent), [.. _virtuals[c.Name]]);
        return new EmittedModule(Names.ClassModule(c.Name), impl) { Interface = iface };
    }

    /// <summary>
    /// R9.18. The virtual methods a class dispatches: its ancestors' first, in the order
    /// they were declared, then its own. It is the order the vtable type declares its
    /// slots in, and every subclass — however deep — fills that one vtable, so the order
    /// has to be a function of the class alone and not of who is asking.
    /// </summary>
    private ImmutableArray<IrMethod> Visible(IrClass c)
    {
        var result = ImmutableArray.CreateBuilder<IrMethod>();
        if (c.BaseClass is { } b && _classes.TryGetValue(b, out var super)) result.AddRange(Visible(super));
        result.AddRange(_virtuals[c.Name].Where(HierarchyEmitter.Admissible));
        return result.ToImmutable();
    }

    // =======================================================================
    // [Spec] functions (R4.6)
    // =======================================================================

    private EmittedModule EmitSpecFunction(IrSpecFunction fn)
    {
        var scope = new SpecScope();
        var binders = new List<string>();

        // R14.2. Type binders first, so that a value binder may mention them.
        foreach (var t in fn.TypeParameters)
        {
            binders.Add($"({Names.TypeParam(t)}: Type0)");
            scope.Bind(t, new Term(Names.TypeParam(t), TermKind.Other));
        }

        foreach (var p in fn.Parameters)
        {
            var name = Names.Local(p.Name);
            switch (p.Type)
            {
                case IrArrayType a:
                    binders.Add($"({name}: Seq.seq {Types.Atom(a.Element)})");
                    scope.Bind(p.Name, new Term(name, TermKind.Seq, p.Type));
                    break;
                // R17.6. A span parameter of a [Spec] method is its contents, exactly
                // as an array parameter is: a pure function has no resources to hold.
                case IrSpanType a:
                    binders.Add($"({name}: Seq.seq {Types.Atom(a.Element)})");
                    scope.Bind(p.Name, new Term(name, TermKind.Seq, p.Type));
                    break;
                case IrPrim { IsMachineInt: true }:
                    // R4.6: a [Spec] method's integer parameters are mathematical.
                    binders.Add($"({name}: int)");
                    scope.Bind(p.Name, new Term(name, TermKind.Math, p.Type));
                    break;
                default:
                    binders.Add($"({name}: {Types.Render(p.Type)})");
                    scope.Bind(p.Name, new Term(name, TermKind.Other, p.Type));
                    break;
            }
        }

        // R4.6: the [Requires] clauses refine the last binder, so that the body
        // type-checks under them.
        if (fn.Requires.Length > 0 && binders.Count > fn.TypeParameters.Length)
        {
            var refinement = SpecEmitter.Conjunction(fn.Requires.Select(r => _spec.AsProp(_spec.Emit(r, scope))));
            var last = binders[^1];
            binders[^1] = last[..^1] + " { " + refinement + " })";
        }

        var (returnType, text) = fn.ReturnType switch
        {
            _ when fn.PulseBody is { } raw => (fn.ReturnType switch
            {
                IrPrim { Kind: PrimKind.Bool } => "prop",
                IrPrim { IsMachineInt: true } => "int",
                _ => Types.Render(fn.ReturnType),
            }, Antiquotation.Expand(raw, scope)),
            IrPrim { Kind: PrimKind.Bool } => ("prop", _spec.AsProp(_spec.Emit(fn.Body, scope))),
            // R4.6: a [Spec] method's integer result is mathematical for the same reason
            // its parameters are — a specification carries no overflow obligation.
            IrPrim { IsMachineInt: true } => ("int", _spec.Math(fn.Body, scope)),
            _ => (Types.Render(fn.ReturnType), _spec.Emit(fn.Body, scope).Text),
        };

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.SpecModule(fn.Name)}");
        sb.AppendLine();
        foreach (var open in Dependencies(
                     Names.SpecModule(fn.Name), null, fn.Requires, [fn.Body]))
            sb.AppendLine($"open {open}");
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        sb.Append(fn.IsRecursive ? "let rec " : "let ").Append(Names.SpecFunction(fn.Name));
        foreach (var b in binders) sb.Append(' ').Append(b);
        sb.AppendLine();
        // A measure belongs to the effect annotation, so a recursive definition is
        // written `: Tot t (decreases m)` rather than `: t`.
        sb.AppendLine(fn.IsRecursive && fn.Decreases is not null
            ? $"  : Tot {returnType} (decreases {_spec.Math(fn.Decreases, scope)})"
            : $"  : {returnType}");
        sb.AppendLine($"  = {text}");

        return new EmittedModule(Names.SpecModule(fn.Name), sb.ToString());
    }

    // =======================================================================
    // [Lemma] declarations (R4.7)
    // =======================================================================

    /// <summary>
    /// A <c>[Lemma]</c> is a proof step about the values the program actually holds at
    /// the point it is applied, so — unlike a <c>[Spec]</c> function (R4.6) — its
    /// parameters keep the program's types: <c>int</c> is <c>I32.t</c>, and an array is
    /// its contents sequence. It becomes an ordinary F* <c>Lemma</c>, which is exactly
    /// what Pulse admits as a ghost statement.
    /// </summary>
    private EmittedModule EmitLemma(IrMethod lemma)
    {
        var scope = new SpecScope { ResultTerm = Names.Result };
        var binders = new List<string>();

        // R14.2. Type binders first, so that a value binder may mention them. They are also
        // bound in the specification scope: R4.9's `$(x)` resolves a C# name to the Pulse
        // term that stands for it, and a type parameter is such a name. Without this, a
        // `[PulseBody]` on a generic lemma whose value arguments do not mention `T` — an
        // introduction rule for the empty case of a predicate, say — has no way to say
        // which type it is about, and the implicit is left as an unresolved uvar.
        foreach (var t in lemma.TypeParameters)
        {
            binders.Add($"({Names.TypeParam(t)}: Type0)");
            scope.Bind(t, new Term(Names.TypeParam(t), TermKind.Other));
        }

        foreach (var p in lemma.Parameters)
        {
            var name = Names.Local(p.Name);
            var (rendered, kind) = p.Type switch
            {
                IrArrayType a => ($"Seq.seq {Types.Atom(a.Element)}", TermKind.Seq),
                IrSpanType a => ($"Seq.seq {Types.Atom(a.Element)}", TermKind.Seq),
                IrSeqType s => ($"Seq.seq {Types.Atom(s.Element)}", TermKind.Seq),
                IrGhostType g => (Types.Render(g.Inner), MethodPlan.KindOf(g.Inner)),
                _ => (Types.Render(p.Type), MethodPlan.KindOf(p.Type)),
            };
            binders.Add($"({name}: {rendered})");
            scope.Bind(p.Name, new Term(name, kind, p.Type));
        }

        // R12.7. A lemma whose contract mentions ownership is a *ghost function*, not an
        // F* `Lemma`. The two are told apart by exactly the test R12.2 already applies to
        // a method's clauses — an `SlProp` clause is a resource — so nothing new is
        // declared and a lemma about pure values is emitted as before, byte for byte.
        static bool IsResource(IrExpr e) => e.Type is IrPrim { Kind: PrimKind.SlProp };
        var isGhostFn = lemma.Requires.Concat(lemma.Ensures).Concat(lemma.Preserves).Any(IsResource);

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.SpecModule(lemma.Name)}");
        if (isGhostFn) sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        foreach (var open in Dependencies(
                     Names.SpecModule(lemma.Name), null, lemma.Requires, lemma.Ensures, lemma.Preserves))
            sb.AppendLine($"open {open}");
        if (isGhostFn)
        {
            sb.AppendLine(Preamble.Opens);
            sb.AppendLine();
        }
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();

        var body = lemma switch
        {
            { Admit: true } => "admit()",
            { PulseBody: { } raw } => Antiquotation.Expand(raw, scope),
            _ => "()",
        };

        if (isGhostFn)
        {
            // The clauses are assembled exactly as R12.2 assembles a method's: resources
            // separated by `**`, everything else inside one `pure`. `[Preserves]` appears
            // on both sides, which is what the word means.
            string Clause(IEnumerable<IrExpr> resources, IEnumerable<string> propositions)
            {
                var res = resources.Select(r => _spec.Emit(r, scope).Text).ToList();
                var pure = SpecEmitter.Conjunction(propositions);
                if (pure != "True") res.Add($"pure ({pure})");
                return res.Count == 0 ? "emp" : string.Join(" **\n           ", res);
            }

            var pre = lemma.Requires.Where(r => !IsResource(r))
                .Select(r => _spec.AsProp(_spec.Emit(r, scope))).ToImmutableArray();
            var post = lemma.Ensures.Where(e => !IsResource(e))
                .Concat(lemma.Preserves.Where(e => !IsResource(e)))
                .Select(e => _spec.AsProp(_spec.Emit(e, scope))).ToImmutableArray();

            sb.Append("ghost fn ").Append(Names.Lemma(lemma.Name));
            foreach (var b in binders) sb.Append(' ').Append(b);
            sb.AppendLine();
            sb.AppendLine("  requires " + Clause(
                lemma.Requires.Where(IsResource).Concat(lemma.Preserves.Where(IsResource)), pre));
            // R4.8, at a lemma. A Pulse `ghost fn`'s `ensures` is type-checked without its
            // `requires` in scope, exactly as a method's is, so a postcondition that reports
            // `l[i]` is ill-typed until `i < l.Length` is restated as a hypothesis. An F*
            // `Lemma` needs none of this — there the `requires` *is* in scope — which is why
            // the pure-lemma form below is untouched.
            sb.AppendLine("  ensures  " + Clause(
                lemma.Ensures.Where(IsResource).Concat(lemma.Preserves.Where(IsResource)),
                MethodPlan.UnderPrecondition(pre, post)));
            sb.AppendLine("{");
            sb.AppendLine($"  {body}");
            sb.AppendLine("}");
            return new EmittedModule(Names.SpecModule(lemma.Name), sb.ToString());
        }

        var requires = SpecEmitter.Conjunction(lemma.Requires.Select(r => _spec.AsProp(_spec.Emit(r, scope))));
        var ensures = SpecEmitter.Conjunction(
            lemma.Ensures.Concat(lemma.Preserves).Select(e => _spec.AsProp(_spec.Emit(e, scope))));

        sb.Append("let ").Append(Names.Lemma(lemma.Name));
        foreach (var b in binders) sb.Append(' ').Append(b);
        sb.AppendLine();
        sb.AppendLine($"  : Lemma (requires ({requires}))");
        sb.AppendLine($"          (ensures ({ensures}))");
        sb.AppendLine($"  = {body}");

        return new EmittedModule(Names.SpecModule(lemma.Name), sb.ToString());
    }

    // =======================================================================
    // Structs (R3.4)
    // =======================================================================

    /// <summary>
    /// A C# <c>struct</c> is a value — it has no identity, assignment copies it, and
    /// nothing can hold a pointer into the middle of one — so it needs an F* record and
    /// nothing else. Where PAL emits a spec type, fold/unfold predicates and per-field
    /// pointer projectors, all of that machinery exists to model C's interior pointers,
    /// which C# does not have.
    /// </summary>
    // =======================================================================
    // Exceptions (§19)
    // =======================================================================

    /// <summary>
    /// R19.1. One module declares every exception class of the program. Each concrete
    /// class is an F* <c>exception</c> carrying a record of all its fields, inherited ones
    /// included; each class, abstract or not, is the refinement of <c>exn</c> to its
    /// discriminator, which matches the exceptions of the class and of its subclasses.
    /// That is the whole of C#'s subtyping on exceptions: a handler for <c>B</c> catches a
    /// <c>D : B</c> because <c>exn_B__is</c> holds of it, and a field of <c>B</c> read
    /// through a <c>D</c> is the accessor's <c>D</c> case.
    /// </summary>
    private static EmittedModule EmitExceptions(ImmutableArray<IrException> exceptions)
    {
        var byName = exceptions.ToDictionary(e => e.Name);
        bool Below(IrException e, string ancestor)
        {
            for (var at = e; at is not null; at = at.Base is { } b && byName.TryGetValue(b, out var up) ? up : null)
                if (at.Name == ancestor) return true;
            return false;
        }
        var concrete = exceptions.Where(e => !e.IsAbstract).ToImmutableArray();

        var sb = new StringBuilder();
        var origin = ImmutableArray.CreateBuilder<Provenance>();
        sb.AppendLine($"module {Names.ExceptionsModule}");
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);

        foreach (var e in concrete)
        {
            sb.AppendLine();
            if (e.Fields.IsEmpty)
            {
                sb.AppendLine($"exception {Names.ExnCtor(e.Name)}");
            }
            else
            {
                sb.AppendLine($"noeq type {Names.ExnPayload(e.Name)} = {{");
                foreach (var f in e.Fields)
                    sb.AppendLine($"  {Names.ExnPayloadField(e.Name, f.Name)}: {Types.Render(f.Type)};");
                sb.AppendLine("}");
                sb.AppendLine($"exception {Names.ExnCtor(e.Name)} of {Names.ExnPayload(e.Name)}");
                origin.Add(new Provenance(Names.ExnPayload(e.Name), e.Loc));
            }
            origin.Add(new Provenance(Names.ExnCtor(e.Name), e.Loc));
        }

        string Pattern(IrException d, string payload) =>
            d.Fields.IsEmpty ? Names.ExnCtor(d.Name) : $"{Names.ExnCtor(d.Name)} {payload}";

        foreach (var e in exceptions)
        {
            var cases = concrete.Where(d => Below(d, e.Name)).ToList();
            sb.AppendLine();
            sb.AppendLine($"let {Names.ExnIs(e.Name)} (e: exn) : bool =");
            sb.AppendLine("  match e with");
            foreach (var d in cases) sb.AppendLine($"  | {Pattern(d, "_")} -> true");
            sb.AppendLine("  | _ -> false");
            sb.AppendLine();
            sb.AppendLine($"type {Names.ExnType(e.Name)} = e: exn {{ {Names.ExnIs(e.Name)} e }}");
            origin.Add(new Provenance(Names.ExnIs(e.Name), e.Loc));
            origin.Add(new Provenance(Names.ExnType(e.Name), e.Loc));

            foreach (var f in e.Fields)
            {
                sb.AppendLine();
                sb.AppendLine($"let {Names.ExnField(e.Name, f.Name)} (e: {Names.ExnType(e.Name)}) : {Types.Render(f.Type)} =");
                if (cases.Count == 0)
                {
                    sb.AppendLine("  false_elim ()");
                }
                else
                {
                    sb.AppendLine("  match e with");
                    foreach (var d in cases)
                        sb.AppendLine($"  | {Pattern(d, "p")} -> p.{Names.ExnPayloadField(d.Name, f.Name)}");
                }
                origin.Add(new Provenance(Names.ExnField(e.Name, f.Name), f.Loc));
            }

            if (e.IsAbstract || e.Ctor is not { } ctor) continue;
            sb.AppendLine();
            var binders = ctor.IsEmpty
                ? "(_: unit)"
                : string.Join(" ", ctor.Select(p => $"({Names.Argument(p.Name)}: {Types.Render(p.Type)})"));
            sb.AppendLine($"let {Names.ExnNew(e.Name)} {binders} : {Names.ExnType(e.Name)} =");
            if (e.Fields.IsEmpty)
            {
                sb.AppendLine($"  {Names.ExnCtor(e.Name)}");
            }
            else
            {
                var inits = e.Fields.Select((f, i) =>
                    $"{Names.ExnPayloadField(e.Name, f.Name)} = " + (e.Inits[i] switch
                    {
                        IrVar v => Names.Argument(v.Name),
                        IrLiteral l => Types.Literal(l.Value, f.Type),
                        _ => "()",
                    }));
                sb.AppendLine($"  {Names.ExnCtor(e.Name)} {{ {string.Join("; ", inits)} }}");
            }
            origin.Add(new Provenance(Names.ExnNew(e.Name), e.Loc));
        }

        return new EmittedModule(Names.ExceptionsModule, sb.ToString()) { Origin = origin.ToImmutable() };
    }

    private EmittedModule EmitStruct(IrStruct s)
    {
        var scope = new SpecScope();
        foreach (var f in s.Fields)
            // Inside the defining module the field name needs no qualifier — and must
            // not have one, or F*'s dependency scan reads the module as depending on
            // itself.
            scope.Bind(f.Name, new Term(
                $"this.{Names.Field(f.Name)}", MethodPlan.KindOf(f.Type), f.Type));

        var predicate = s.Refinements.Length == 0
            ? "True"
            : SpecEmitter.Conjunction(s.Refinements.Select(r => _spec.AsProp(_spec.Emit(r, scope))));

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.StructModule(s.Name)}");
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        // R22.6. A generic `[Spec]` struct's parameters are explicit on the two types and
        // implicit on the predicate, as R15.2 has them for a class.
        var binders = new TypeBinders(s.TypeParameters);
        sb.Append("noeq type ").Append(Names.StructRaw(s.Name)).Append(binders.Explicit).AppendLine(" = {");
        foreach (var f in s.Fields)
            sb.AppendLine($"  {Names.Field(f.Name)}: {Types.Render(f.Type)};");
        sb.AppendLine("}");
        sb.AppendLine();
        // The refinement predicate is emitted even when trivial: uniform output beats
        // output whose shape depends on whether the user happened to write [Refine].
        sb.AppendLine($"let {Names.StructPred(s.Name)}{binders.Implicit} (this: {binders.App(Names.StructRaw(s.Name))}) : prop =");
        sb.AppendLine($"  {predicate}");
        sb.AppendLine();
        sb.AppendLine($"type {Names.StructType(s.Name)}{binders.Explicit} = " +
                      $"this: {binders.App(Names.StructRaw(s.Name))} {{ {Names.StructPred(s.Name)} this }}");

        // R24.11. An unrefined struct of defaultable fields has C#'s `default(S)`, all
        // fields defaulted, so an array of it can be allocated and cleared.
        if (!s.IsSpecOnly && s.Refinements.Length == 0 &&
            s.Fields.All(f => f.Type is IrPrim { IsMachineInt: true } or IrPrim { Kind: PrimKind.Bool }
                                          or IrTypeParamType))
        {
            var needs = string.Concat(s.TypeParameters.Select(p =>
                $" {{| Pulse.Lib.CSharp.Inhabited.has_default {Names.TypeParam(p)} |}}"));
            sb.AppendLine();
            sb.AppendLine($"instance {Names.StructType(s.Name)}__has_default{binders.Implicit}{needs} : " +
                          $"Pulse.Lib.CSharp.Inhabited.has_default {binders.App(Names.StructType(s.Name))} = {{");
            sb.AppendLine("  default_value = {");
            foreach (var f in s.Fields)
                sb.AppendLine($"    {Names.Field(f.Name)} = Pulse.Lib.CSharp.Inhabited.default_value;");
            sb.AppendLine("  }");
            sb.AppendLine("}");
        }

        return new EmittedModule(Names.StructModule(s.Name), sb.ToString());
    }

    // =======================================================================
    // Classes (§3.4)
    // =======================================================================

    /// <summary>
    /// A C# <c>class</c> is a heap cell with identity, so — unlike a struct (R3.4) — it
    /// needs a <c>Box</c> and a model-indexed invariant. One module carries the whole
    /// type: the representation, the object-reference type, the refined model type, the
    /// invariant, and each <c>[Spec]</c> observation. Method modules open it.
    /// </summary>
    /// <summary>R3.10b. The sub-object's invariant, qualified by its own module.</summary>
    internal static string SubInv(IrType t) =>
        $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassInv(((IrClassType)t).Name)}";

    /// <summary>
    /// R3.10b/R10.3. The sub-object's invariant <em>applied</em>. A nullable field is owned
    /// through the recursive `__inv_opt`, whose permission is an ordinary positional binder
    /// (F36c: a `let rec` cannot carry R3.10c's meta-defaulted one, because the recursive
    /// call instantiates it). Every site that owns a field's invariant goes through here, so
    /// the difference is stated once and no other rule knows about it.
    /// </summary>
    /// <summary>
    /// The same, taking the permission in the form a <see cref="Slot"/> carries it —
    /// <c>"#p "</c> for a fraction, empty for full ownership. R3.10c's default makes the
    /// empty form mean <c>1.0R</c>, which R10.3's positional binder has to be told.
    /// </summary>
    internal static string SubInvAt(IrType t, string reference, string permArg, string model) =>
        ((IrClassType)t).Nullable
            ? SubInvApp(t, reference, permArg.Length == 0 ? "1.0R" : permArg.Trim().TrimStart('#'), model)
            : $"{SubInv(t)} {reference} {permArg}{model}";

    internal static string SubInvApp(IrType t, string reference, string perm, string model)
    {
        var k = (IrClassType)t;
        return k.Nullable
            ? $"{Names.ClassModule(k.Name)}.{Names.ClassInvOpt(k.Name)} {reference} {perm} {model}"
            : $"{Names.ClassModule(k.Name)}.{Names.ClassInv(k.Name)} {reference} #{perm} {model}";
    }

    /// <summary>R3.10b. The sub-object's model type, qualified by its own module.</summary>
    internal static string SubModelType(IrType t) =>
        Types.Applied(
            $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassModel(((IrClassType)t).Name)}",
            ((IrClassType)t).TypeArguments);

    /// <summary>R3.10d. A sub-object's own <c>share</c>, qualified by its module.</summary>
    private static string SubShare(IrType t) =>
        ((IrClassType)t).Nullable
            ? $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassInvOptShare(((IrClassType)t).Name)}"
            : $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassInvShare(((IrClassType)t).Name)}";

    /// <summary>R3.10d. A sub-object's general <c>gather</c>, qualified by its module.</summary>
    private static string SubGatherGen(IrType t) =>
        ((IrClassType)t).Nullable
            ? $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassInvOptGather(((IrClassType)t).Name)}"
            : $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassInvGatherGen(((IrClassType)t).Name)}";

    /// <summary>
    /// R12.1. The whole of a <c>[Plain]</c> class: the record of fields, the reference,
    /// and the nullable reference — the same three lines §10 emits (F35), and then nothing.
    ///
    /// <para>No invariant, because the user writes it. No model type, because there is no
    /// abstraction function to give one. No case lemmas, because the cases are a property
    /// of the user's predicate and not of this record. What the module exports is exactly
    /// what a user's Pulse module needs in order to <em>state</em> ownership: a type to
    /// hold <c>B.pts_to</c> at, and field names to write equations over.</para>
    /// </summary>
    private string EmitPlainClass(IrClass c)
    {
        var tb = TypeBinders.Of(c);
        var raw = tb.App(Names.ClassRaw(c.Name));
        var self = tb.App(Names.ClassType(c.Name));
        var opt = tb.App(Names.ClassOpt(c.Name));

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.ClassModule(c.Name)}");
        sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        sb.AppendLine(Preamble.Opens);
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();

        // F35. The three declarations are one mutually recursive group whether or not the
        // class actually refers to itself, which costs nothing and means a self-reference
        // needs no separate rule.
        // R31.2. An owner that its region's nodes point back to has its record in this
        // group, so neither module depends on the other.
        var group = CycleOwners(c);
        string Local(string t) => group.Aggregate(t.Replace(Names.ClassModule(c.Name) + ".", ""),
            (acc, d) => acc.Replace(Names.ClassModule(d.Name) + ".", ""));
        sb.Append("noeq type ").Append(Names.ClassRaw(c.Name)).Append(tb.Explicit).AppendLine(" = {");
        foreach (var f in c.Fields)
            sb.AppendLine($"  {Names.Field(f.Name)}: {Local(PlainFieldType(c, f.Type, opt, self))};");
        sb.AppendLine("}");
        sb.AppendLine($"and {Names.ClassOpt(c.Name)}{tb.Explicit} = B.box {raw}");
        sb.AppendLine($"and {Names.ClassType(c.Name)}{tb.Explicit} = b: {opt} {{ not (B.is_null b) }}");
        foreach (var d in group)
        {
            var db = TypeBinders.Of(d);
            sb.Append("and ").Append(Names.ClassRaw(d.Name)).Append(db.Explicit).AppendLine(" = {");
            foreach (var f in d.Fields)
                sb.AppendLine($"  {Names.Field(f.Name)}: {Local(Types.Render(f.Type))};");
            sb.AppendLine("}");
            sb.AppendLine($"and {Names.ClassOpt(d.Name)}{db.Explicit} = B.box {db.App(Names.ClassRaw(d.Name))}");
        }
        if (c.IsRegion) EmitRegionShape(sb, c, tb, raw, opt);
        return sb.ToString();
    }

    /// <summary>
    /// R31.3. Whether a class's invariant or abstraction names <c>@this</c>, so that the
    /// functions stating it of a record take the reference first.
    /// </summary>
    internal static bool InvariantNamesThis(IrClass c) =>
        c.Invariants.Concat(c.ModelBody is null ? [] : [c.ModelBody])
            .SelectMany(Passes.Check.Subexpressions).OfType<IrVar>().Any(v => v.Name == Names.This);

    /// <summary>
    /// R31.2. The owners whose records a <c>[Region]</c> class's module declares: each
    /// translated, non-plain class that holds a pointer into the region and is pointed back
    /// to by a field of the region class.
    /// </summary>
    private ImmutableArray<IrClass> CycleOwners(IrClass c) =>
        !c.IsRegion ? [] :
        [.. c.Fields.Select(f => f.Type).OfType<IrClassType>().Select(t => t.Name).Distinct()
            .Where(n => n != c.Name && _classes.TryGetValue(n, out var d) && !d.IsPlain &&
                        d.Recursion is null && !d.InHierarchy &&
                        d.Fields.Any(g => g.Type is IrClassType gt && gt.Name == c.Name))
            .Select(n => _classes[n])];

    /// <summary>R31.2. The region class whose module declares this owner's record, if any.</summary>
    private IrClass? CycleRegionOf(IrClass d) =>
        _classes.Values.FirstOrDefault(c => CycleOwners(c).Any(o => o.Name == d.Name));

    /// <summary>
    /// R27.7. What a <c>[Region]</c> class adds to its representation: the two child
    /// projections, the view of one node, and the tree and well-formedness a pointer has in
    /// a heap, both instances of <c>Pulse.Lib.CSharp.Region</c>'s generic definitions.
    /// </summary>
    private void EmitRegionShape(StringBuilder sb, IrClass c, TypeBinders tb, string raw, string opt)
    {
        var children = c.Fields
            .Where(f => f.Type is IrClassType { Nullable: true } ct && ct.Name == c.Name)
            .Take(2).ToArray();
        // R31.2. The owners declared in this module are named unqualified here.
        var group = CycleOwners(c);
        string Local(string t) => group.Aggregate(t, (acc, d) => acc.Replace(Names.ClassModule(d.Name) + ".", ""));
        var viewType = c.ModelBody is null ? "unit" : Local(Types.Render(c.ModelType));
        var scope = new SpecScope { DefiningClass = c.Name };
        foreach (var f in c.Fields)
            scope.Bind(f.Name, new Term($"r.{Names.Field(f.Name)}", MethodPlan.KindOf(f.Type), f.Type));
        var view = c.ModelBody is null ? "()" : Local(_spec.Emit(c.ModelBody, scope).Text);
        var R = Frontend.Region.Module;
        var heap = $"{R}.heap {raw}";
        string App(string f) => tb.Explicit.Length == 0 ? f : $"({f}{string.Concat(c.TypeParameters.Select(t => " #" + Names.TypeParam(t)))})";
        sb.AppendLine();
        sb.AppendLine($"let {Frontend.Region.LeftOf(c.Name)}{tb.Implicit} (r: {raw}) : {opt} = r.{Names.Field(children[0].Name)}");
        sb.AppendLine($"let {Frontend.Region.RightOf(c.Name)}{tb.Implicit} (r: {raw}) : {opt} = r.{Names.Field(children[1].Name)}");
        sb.AppendLine($"let {Frontend.Region.ViewOf(c.Name)}{tb.Implicit} (this: {opt}) (r: {raw}) : {viewType} = {view}");
        // R31.1. A ring has no tree, and a read needs only that the node is in the region.
        if (c.IsCyclic)
        {
            sb.AppendLine();
            sb.AppendLine($"inline_for_extraction noextract");
            sb.AppendLine($"fn {Frontend.Region.ReadOf(c.Name)}{tb.Implicit} (x: {opt}) (#p: perm) (#h: erased ({heap}))");
            sb.AppendLine($"  preserves {R}.region #{Types.Atom(new IrPulseType(raw, raw))} #p h");
            sb.AppendLine($"  requires pure ({R}.mem h x)");
            sb.AppendLine($"  returns v: {raw}");
            sb.AppendLine($"  ensures pure ({R}.mem h x /\\ not (B.is_null x) /\\ v == {R}.get h x)");
            sb.AppendLine("{");
            sb.AppendLine($"  {R}.read x");
            sb.AppendLine("}");
            return;
        }
        var shape = $"{App(Frontend.Region.ViewOf(c.Name))} {App(Frontend.Region.LeftOf(c.Name))} {App(Frontend.Region.RightOf(c.Name))}";
        var lr = $"{App(Frontend.Region.LeftOf(c.Name))} {App(Frontend.Region.RightOf(c.Name))}";
        sb.AppendLine($"let {Frontend.Region.TreeOf(c.Name)}{tb.Implicit} (h: {heap}) (x: {opt}) " +
                      $": GTot (Pulse.Lib.CSharp.Tree.tree ({viewType})) = {R}.tree_of {shape} h x");
        sb.AppendLine($"let {Frontend.Region.WfOf(c.Name)}{tb.Implicit} (h: {heap}) (x: {opt}) : prop = {R}.wf {lr} h x");
        // R27.16. The shape facts a method that writes the region states.
        var RT = Frontend.Region.TreeModule;
        sb.AppendLine($"let {Frontend.Region.UnsharedOf(c.Name)}{tb.Implicit} (h: {heap}) (x: {opt}) : prop = {RT}.unshared {lr} h x");
        sb.AppendLine($"let {Frontend.Region.ReshapedOf(c.Name)}{tb.Implicit} (h0 h1: {heap}) (x y: {opt}) : prop = {RT}.reshaped {lr} h0 h1 x y");
        sb.AppendLine();
        // R27.5. A read through the region, with the step a descent takes for free.
        sb.AppendLine($"inline_for_extraction noextract");
        sb.AppendLine($"fn {Frontend.Region.ReadOf(c.Name)}{tb.Implicit} (x: {opt}) (#p: perm) (#h: erased ({heap}))");
        sb.AppendLine($"  preserves {R}.region #{Types.Atom(new IrPulseType(raw, raw))} #p h");
        sb.AppendLine($"  requires pure ({R}.mem h x \\/ ({Frontend.Region.WfOf(c.Name)} h x /\\ not (B.is_null x)))");
        sb.AppendLine($"  returns v: {raw}");
        sb.AppendLine($"  ensures pure ({R}.mem h x /\\ v == {R}.get h x /\\");
        sb.AppendLine($"                ({Frontend.Region.WfOf(c.Name)} h x ==>");
        sb.AppendLine($"                  ({Frontend.Region.WfOf(c.Name)} h ({Frontend.Region.LeftOf(c.Name)} v) /\\");
        sb.AppendLine($"                   {Frontend.Region.WfOf(c.Name)} h ({Frontend.Region.RightOf(c.Name)} v) /\\");
        sb.AppendLine($"                   {Frontend.Region.TreeOf(c.Name)} h x == Pulse.Lib.CSharp.Tree.Branch");
        sb.AppendLine($"                     ({Frontend.Region.TreeOf(c.Name)} h ({Frontend.Region.LeftOf(c.Name)} v))");
        sb.AppendLine($"                     ({Frontend.Region.ViewOf(c.Name)} x v)");
        sb.AppendLine($"                     ({Frontend.Region.TreeOf(c.Name)} h ({Frontend.Region.RightOf(c.Name)} v)))))");
        sb.AppendLine("{");
        sb.AppendLine($"  {R}.mem_of_wf {lr} h x;");
        sb.AppendLine($"  let v = {R}.read x;");
        sb.AppendLine($"  {R}.wf_step_if {shape} h x;");
        sb.AppendLine("  v");
        sb.AppendLine("}");
    }

    /// <summary>
    /// R27.13. The regions of an instance method's receiver, when its contract names one of
    /// their heaps; otherwise none, and the receiver is held at the plain invariant.
    /// </summary>
    private ImmutableArray<IrClassType> HeapRegions(IrMethod m)
    {
        if (m.DeclaringClass is null || m.IsConstructor || m.Overrides is not null) return [];
        if (!_classes.TryGetValue(m.DeclaringClass, out var c) || c.IsPlain) return [];
        var regions = c.Fields.Where(IsRegionField).Select(f => (IrClassType)f.Type)
            .GroupBy(t => t.Name).Select(g => g.First()).ToImmutableArray();
        if (regions.IsEmpty) return [];
        if (m.Open) return regions;
        var names = m.Requires.Concat(m.Ensures).Concat(m.Preserves)
            .SelectMany(Passes.Check.Subexpressions)
            .OfType<IrVar>().Select(v => v.Name).ToImmutableHashSet();
        if (regions.Any(k => names.Contains(Frontend.Region.HeapName(k.Name)))) return regions;
        // R27.41. A method that holds a borrowing struct of its object holds it at its heaps,
        // which the struct's members are passed, as do the loops that name them.
        if (m.Body is not null && Passes.Check.Statements(m.Body).Any(st =>
                st is IrLocalDecl { Owned.IsDefaultOrEmpty: false } ||
                Passes.Check.Expressions(st).SelectMany(Passes.Check.Subexpressions)
                    .OfType<IrVar>().Any(v => regions.Any(k => v.Name == Frontend.Region.HeapName(k.Name)))))
            return regions;
        // R27.50. A read-only method gives its heaps back as it found them, so a caller
        // keeps what it knew of them across the call.
        if (m.IsReadOnly && !m.IsAbstract) return regions;
        return _heapsKept.Contains(m.Name) ? regions : [];
    }

    /// <summary>
    /// R27.38. An owner's method whose body names no value of a region class (it reads no
    /// region field and holds no node) leaves its regions alone: it is held at its heaps,
    /// and gives them back unchanged, so a caller part-way through a traversal keeps what
    /// it knew of them (`IsWithinRange`, `VersionCheck`). Nothing rests on the test: the
    /// body is verified against the contract it selects.
    /// </summary>
    private HashSet<string> HeapsKept(ImmutableArray<IrMethod> methods)
    {
        bool IsRegion(IrType? t) => t is IrClassType k && _classes.TryGetValue(k.Name, out var d) && d.IsRegion;
        bool Base(IrMethod m)
        {
            if (m.Body is null || m.IsLemma || m.Open || m.IsConstructor || m.Overrides is not null) return false;
            if (m.DeclaringClass is not { } dc || !_classes.TryGetValue(dc, out var c) || c.IsPlain ||
                !c.Fields.Any(IsRegionField))
                return false;
            if (m.Requires.Concat(m.Ensures).Concat(m.Preserves).SelectMany(Passes.Check.Subexpressions)
                .OfType<IrVar>().Any(v => v.Name.StartsWith(Frontend.Region.HeapName(""))))
                return false;
            if (m.Parameters.Any(p => IsRegion(p.Type)) || IsRegion(m.ReturnType)) return false;
            foreach (var st in Passes.Check.Statements(m.Body))
            {
                if (st is IrLocalDecl ld && IsRegion(ld.Type)) return false;
                if (Passes.Check.Expressions(st).SelectMany(Passes.Check.Subexpressions).Any(e => IsRegion(e.Type)))
                    return false;
            }
            return true;
        }
        // The calls a kept method makes on an object are its own calls, on `this`, to kept
        // methods: the greatest such set.
        var kept = methods.Where(Base).GroupBy(m => m.Name).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.First());
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var entry in kept.ToList())
            {
                var (name, m) = (entry.Key, entry.Value);
                var ok = Passes.Check.Statements(m.Body!).SelectMany(Passes.Check.Expressions)
                    .SelectMany(Passes.Check.Subexpressions).OfType<IrCall>()
                    .All(c => !c.HasReceiver ||
                              c.Args is [IrVar { Name: Names.This }, ..] && kept.ContainsKey(c.Callee));
                if (!ok) { kept.Remove(name); changed = true; }
            }
        }
        return [.. kept.Keys];
    }

    /// <summary>R27.38. The owner methods held at their heaps that give them back unchanged.</summary>
    private HashSet<string> _heapsKept = [];

    /// <summary>
    /// R27.16. The regions a method that is not an owner's holds itself: those of the region
    /// classes it is a member of, takes, returns, reads, allocates or calls into, each with
    /// whether it writes the region (a field write, an allocation, or a call that writes).
    /// The write set is a fixpoint over the call graph.
    /// </summary>
    private Dictionary<string, ImmutableArray<RegionUse>> RegionHeld(ImmutableArray<IrMethod> methods)
    {
        bool IsRegion(IrType? t) => t is IrClassType k && _classes.TryGetValue(k.Name, out var d) && d.IsRegion;
        bool OwnerMethod(IrMethod m) =>
            m.DeclaringClass is { } dc && _classes.TryGetValue(dc, out var c) && !c.IsPlain &&
            c.Fields.Any(IsRegionField);
        var touched = new Dictionary<string, Dictionary<string, IrClassType>>();
        var writes = new Dictionary<string, HashSet<string>>();
        var calls = new Dictionary<string, List<string>>();
        foreach (var m in methods)
        {
            if (OwnerMethod(m) || m.IsLemma) continue;
            var ks = new Dictionary<string, IrClassType>();
            void Add(IrType? t) { if (IsRegion(t) && !ks.ContainsKey(((IrClassType)t!).Name)) ks[((IrClassType)t!).Name] = ((IrClassType)t!) with { Nullable = false }; }
            foreach (var p in m.Parameters) Add(p.Type);
            Add(m.ReturnType);
            var w = new HashSet<string>();
            var cs = new List<string>();
            if (m.Body is not null)
            {
                foreach (var st in Passes.Check.Statements(m.Body))
                {
                    if (st is IrAssign { Target: IrField { Receiver.Type: IrClassType wk } } && IsRegion(wk))
                    { Add(wk); w.Add(wk.Name); }
                    if (st is IrLocalDecl ld) Add(ld.Type);
                    foreach (var e in Passes.Check.Expressions(st).SelectMany(Passes.Check.Subexpressions))
                    {
                        if (e is IrField { Receiver.Type: IrClassType rk } && IsRegion(rk)) Add(rk);
                        if (e is IrAlloc al && _classes.TryGetValue(al.Class, out var ad) && ad.IsRegion && al.Type is IrClassType at)
                        { Add(at); w.Add(al.Class); }
                        if (e is IrCall call) cs.Add(call.Callee);
                    }
                }
            }
            // R27.59. A region that an object the method's class owns through a field owns is
            // reached through that field, which the body keeps open while it reads the region.
            if (m.DeclaringClass is { } hc && _classes.TryGetValue(hc, out var hdecl) && !hdecl.IsPlain)
                foreach (var f in hdecl.Fields)
                    if (f.Type is IrClassType { } fc && _classes.TryGetValue(fc.Name, out var fdecl) && !fdecl.IsPlain)
                        foreach (var rf in fdecl.Fields.Where(IsRegionField))
                            if (rf.Type is IrClassType rk) { ks.Remove(rk.Name); w.Remove(rk.Name); }
            touched[m.Name] = ks;
            writes[m.Name] = w;
            calls[m.Name] = cs;
        }
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var entry in calls)
                foreach (var callee in entry.Value)
                {
                    if (!touched.TryGetValue(callee, out var ck)) continue;
                    foreach (var kv in ck)
                        if (!touched[entry.Key].ContainsKey(kv.Key)) { touched[entry.Key][kv.Key] = kv.Value; changed = true; }
                    foreach (var kn in writes[callee])
                        if (writes[entry.Key].Add(kn)) changed = true;
                }
        }
        // R27.36. A method that touches no region, and calls only methods that touch none,
        // holds none: a loop calling it (a `Stack<Node>` holding the region's pointers)
        // keeps the region's heap. One calling a method this does not see (an owner's,
        // which holds its region through `this`) is left out, and is assumed to write.
        var opaque = new HashSet<string>(calls.Where(c => c.Value.Any(callee => !touched.ContainsKey(callee))).Select(c => c.Key));
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var entry in calls)
                if (!opaque.Contains(entry.Key) && entry.Value.Any(opaque.Contains)) { opaque.Add(entry.Key); changed = true; }
        }
        return touched.Where(t => t.Value.Count > 0 || !opaque.Contains(t.Key)).ToDictionary(
            t => t.Key,
            t => t.Value.Values.Select(k => new RegionUse(k, writes[t.Key].Contains(k.Name))).ToImmutableArray());
    }

    private Dictionary<string, ImmutableArray<RegionUse>> _regionHeld = [];

    /// <summary>R27.38. The methods with a <c>[Throws]</c>: a call to one may raise.</summary>
    private HashSet<string> _raising = [];

    /// <summary>R27.37. The fields of each borrowing struct that own an object.</summary>
    private Dictionary<string, ImmutableArray<IrFieldDecl>> _ownedFields = [];

    /// <summary>
    /// R27.4, R27.58. Whether a class's invariant can be split into fractions: it owns no
    /// region, and each object it owns can be split.
    /// </summary>
    private bool Shareable(IrClass c, HashSet<string>? visiting = null)
    {
        visiting ??= [];
        if (!visiting.Add(c.Name)) return true;
        return !c.Fields.Any(IsRegionField) &&
               c.Fields.All(f => f.Type is not IrClassType { Name: var n } ||
                                 !_classes.TryGetValue(n, out var owned) || Shareable(owned, visiting));
    }

    private bool IsRegionField(IrFieldDecl f) =>
        f.Type is IrClassType ct && _classes.TryGetValue(ct.Name, out var d) && d.IsRegion;

    /// <summary>R27.4. The record type a region class's heap maps its boxes to.</summary>
    internal static string RegionRaw(IrClassType k) =>
        Types.Applied($"{Names.ClassModule(k.Name)}.{Names.ClassRaw(k.Name)}", k.TypeArguments);

    /// <summary>R27.4. The region resource, at a permission and a heap.</summary>
    internal static string RegionAt(IrClassType k, string perm, string heap) =>
        $"{Frontend.Region.Module}.region #{RegionRaw(k)} #{perm} {heap}";

    /// <summary>A field of a <c>[Plain]</c> class; a self-reference is the nullable form.</summary>
    private static string PlainFieldType(IrClass c, IrType t, string opt, string self) =>
        t is IrClassType ct && ct.Name == c.Name
            ? (ct.Nullable ? opt : self)
            : Types.Render(t);

    private EmittedModule EmitClass(IrClass c)
    {
        // §10. A class that holds its own nullable type cannot have a flat `exists*`
        // invariant: the predicate would appear inside its own definition. Its whole module
        // is a different shape, so it is emitted whole rather than patched — every rule
        // below assumes an invariant with one record and no recursion.
        if (c.Recursion is not null)
            return new EmittedModule(Names.ClassModule(c.Name), _recursive.Emit(c));

        // R12.1. A `[Plain]` class is its representation and nothing else. Everything the
        // rest of this method emits is derived from the model, and there is none.
        if (c.IsPlain)
            return new EmittedModule(Names.ClassModule(c.Name), EmitPlainClass(c));

        // R3.7: inside the defining module a field needs no qualifier, and must not have
        // one, or F*'s dependency scan reads the module as depending on itself.
        var tb0 = TypeBinders.Of(c);
        var repScope = new SpecScope();
        foreach (var f in c.Fields)
        {
            // R3.10a. An array field denotes two different things in the two halves of the
            // invariant: the reference in the `A.pts_to`, and its *contents* everywhere in
            // the `pure`. Binding the field name to the contents is what makes
            // `items.Length` and `Pal.Contents(items)` mean in a class-level clause exactly
            // what they mean in a method contract about an array parameter (R4.4).
            //
            // R3.10b does the same for an object field, and for the same reason: the
            // reference goes in the sub-invariant, and the *model* is what a clause about
            // the field can say anything about. `left.Count` in an [Invariant] then means
            // `spec_D_Count model_left`, which is what it means in a client's contract
            // about an object parameter — one reading of a member access, everywhere.
            var term = f.Type switch
            {
                // R27.4. A pointer into a region is a value; the region is beside it.
                _ when IsRegionField(f) => new Term($"r.{Names.Field(f.Name)}", TermKind.Other, f.Type),
                IrArrayType => new Term(Names.Contents(f.Name), TermKind.Seq, f.Type),
                IrClassType => new Term(Names.SubModel(f.Name), TermKind.Math, f.Type),
                _ => new Term($"r.{Names.Field(f.Name)}", MethodPlan.KindOf(f.Type), f.Type),
            };
            repScope.Bind(f.Name, term);
            if (f.Type is IrArrayType)
                repScope.Bind(SpecEmitter.ArrayRefKey(f.Name), new Term($"r.{Names.Field(f.Name)}", TermKind.Other, f.Type));
        }
        var arrays = c.Fields.Where(f => f.Type is IrArrayType).ToImmutableArray();
        var objects = c.Fields.Where(f => f.Type is IrClassType && !IsRegionField(f)).ToImmutableArray();
        var regionFields = c.Fields.Where(IsRegionField).ToImmutableArray();
        var regions = regionFields.Select(f => (IrClassType)f.Type)
            .GroupBy(t => t.Name).Select(g => g.First()).ToImmutableArray();
        foreach (var k in regions)
            repScope.Bind(Frontend.Region.HeapName(k.Name),
                new Term(Frontend.Region.HeapBinder(k.Name), TermKind.Other));
        // R31.3. `@this` in an [Invariant] is the reference itself: the predicate is of it.
        repScope.Bind(Names.This, new Term("this", TermKind.Other, new IrClassType(c.Name, false)
            { TypeArguments = [.. c.TypeParameters.Select(t => (IrType)new IrTypeParamType(t))] }));
        var thisParam = InvariantNamesThis(c) ? $"(this: {tb0.App(Names.ClassType(c.Name))}) " : "";

        // R3.9d: the model refinement is stated over the model value, which a [Refine]
        // on the [Model] member names `Result`, as an [Ensures] does.
        var modelKind = MethodPlan.KindOf(c.ModelType);
        // R3.9b: the [Invariant] clauses and the abstraction relation are conjuncts of one
        // `pure`, and the order is load-bearing. `p1 /\ p2` types `p2` with `p1` in scope,
        // so the [Invariant] clauses come *first*: they are the bounds that make a partial
        // abstraction such as `Seq.slice contents 0 top` well-typed where it appears.
        // The equation is stated at the model's kind: a `SpecInt` model of an `int` field
        // is that field's mathematical value, so the abstraction carries the `Int32.v` that
        // §6 puts on every integer in spec position.
        var modelBody = c.ModelBody ?? throw new InvalidOperationException(
            $"{c.Name} has no abstraction function");
        var abstraction = modelKind == TermKind.Math
            ? _spec.Math(modelBody, repScope)
            : _spec.Emit(modelBody, repScope).Text;
        var conjuncts = new List<string>();
        // R3.10a. A C# array's length is an `int`, so this bound is a fact about the
        // source type and not an assumption: it enters at `new T[n]`, whose length
        // argument is already an `int`, and rides round every fold from there. It is
        // stated first because it is what makes arithmetic on an index into the array
        // provably non-overflowing.
        foreach (var f in arrays)
            conjuncts.Add($"Seq.length {Names.Contents(f.Name)} <= 2147483647");
        // R27.4. Every pointer the owner holds into a region is unshared in it (R27.16):
        // well-formed, and reaching no box twice.
        foreach (var f in regionFields.Where(f => !_classes[((IrClassType)f.Type).Name].IsCyclic))
        {
            var k = (IrClassType)f.Type;
            conjuncts.Add($"{Names.ClassModule(k.Name)}.{Frontend.Region.UnsharedOf(k.Name)} " +
                          $"{Frontend.Region.HeapBinder(k.Name)} r.{Names.Field(f.Name)}");
        }
        conjuncts.AddRange(c.Invariants.Select(i => _spec.AsProp(_spec.Emit(i, repScope))));
        conjuncts.Add($"m == {abstraction}");

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.ClassModule(c.Name)}");
        sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        sb.AppendLine(Preamble.Opens);
        // R24.17. A `[Spec]` function named by the representation invariant, the model or
        // an observation lives in its own module.
        foreach (var open in ClassSpecOpens(c))
            sb.AppendLine($"open {open}");
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();

        // R3.10c needs `T.exact` for the invariant's defaulted permission binder. The
        // alias is emitted here rather than in the shared preamble because a class module
        // is the only one that has a use for it.
        sb.AppendLine("module T = FStar.Tactics");
        sb.AppendLine();

        var tb = TypeBinders.Of(c);
        // R31.2. A record its region's module declares is included from there.
        if (CycleRegionOf(c) is { } home)
        {
            sb.AppendLine($"include {Names.ClassModule(home.Name)}");
            sb.AppendLine();
        }
        else
        {
            sb.Append("noeq type ").Append(Names.ClassRaw(c.Name)).Append(tb.Explicit).AppendLine(" = {");
            foreach (var f in c.Fields)
                sb.AppendLine($"  {Names.Field(f.Name)}: {Types.Render(f.Type)};");
            sb.AppendLine("}");
            sb.AppendLine();
        }

        // R3.8: a CLR object reference is a `Box.box` of the representation. `Box` is the
        // sound heap cell (F14); `Reference.alloc` is marked unsound and never emitted.
        sb.AppendLine($"let {Names.ClassType(c.Name)}{tb.Explicit} = " +
                      $"B.box {tb.App(Names.ClassRaw(c.Name))}");
        sb.AppendLine();

        // R3.9d. Emitted even when the predicate is `True`, for the same reason
        // `struct_S__pred` is (§0 rule 2): uniform output beats output whose shape
        // depends on whether the user happened to write [Refine].
        _hierarchy.EmitModelType(sb, c);

        // R3.10: the invariant is indexed by the model. An un-indexed `inv (x: C)` puts
        // the object's whole state under an existential, so no postcondition could relate
        // the post-state to the pre-state — memory safety and nothing more.
        //
        // R3.10c: it is also indexed by a *permission*, which propagates to every resource
        // conjunct. The binder is meta-argument-defaulted (F21), so `class_C__inv x m`
        // still means full ownership and no other rule's output changes: the whole feature
        // is reached by asking for it.
        sb.AppendLine($"let {Names.ClassInv(c.Name)}{tb.Implicit} " +
                      $"(this: {tb.App(Names.ClassType(c.Name))}) " +
                      $"(#[T.exact (`1.0R)] p: perm) (m: {tb.App(Names.ClassModel(c.Name))}) : slprop =");
        var existentials = new List<string> { $"(r: {tb.App(Names.ClassRaw(c.Name))})" };
        existentials.AddRange(arrays.Select(f =>
            $"({Names.Contents(f.Name)}: Seq.seq {Types.Atom(((IrArrayType)f.Type).Element)})"));
        existentials.AddRange(objects.Select(f =>
            $"({Names.SubModel(f.Name)}: {SubModelType(f.Type)})"));
        existentials.AddRange(regions.Select(k =>
            $"({Frontend.Region.HeapBinder(k.Name)}: {Frontend.Region.Module}.heap {RegionRaw(k)})"));
        void Body()
        {
            sb.AppendLine("    B.pts_to this #p r **");
            // R27.4. The owner holds the whole region, at the fraction it is itself held at.
            foreach (var k in regions)
                sb.AppendLine($"    {RegionAt(k, "p", Frontend.Region.HeapBinder(k.Name))} **");
            foreach (var f in arrays)
                sb.AppendLine($"    {ArrayPts(f)} r.{Names.Field(f.Name)} #p {Names.Contents(f.Name)} **");
            // R3.10b. The sub-object's own invariant, at its own model. Nesting is one
            // conjunct: the outer invariant does not restate the inner one, it *contains* it,
            // so an inner class's [Invariant] clauses are proved once, where they were written.
            // R3.10c hands it the *same* fraction: an object held at `p` is one every part of
            // which is held at `p`, and there is no other coherent reading.
            foreach (var f in objects)
                sb.AppendLine($"    {SubInvApp(f.Type, $"r.{Names.Field(f.Name)}", "p", Names.SubModel(f.Name))} **");
            sb.AppendLine($"    pure ({SpecEmitter.Conjunction(conjuncts)})");
        }
        sb.AppendLine($"  exists* {string.Join(" ", existentials)}.");
        Body();

        // R27.38. With no array or object field, the pure half of the invariant is a
        // relation of the record, the heaps and the model alone: a loop that reopens the
        // object states it of the record it holds.
        if (arrays.IsEmpty && objects.IsEmpty)
        {
            sb.AppendLine();
            sb.AppendLine($"let {Names.ClassAbs(c.Name)}{tb.Implicit} {thisParam}(r: {tb.App(Names.ClassRaw(c.Name))}) " +
                          string.Concat(regions.Select(k =>
                              $"({Frontend.Region.HeapBinder(k.Name)}: {Frontend.Region.Module}.heap {RegionRaw(k)}) ")) +
                          $"(m: {tb.App(Names.ClassModel(c.Name))}) : prop =");
            sb.AppendLine($"  {SpecEmitter.Conjunction(conjuncts)}");

            // R27.52. With no [Invariant] clause to type it, the abstraction is a function of
            // the record and the heaps, and the rest of the relation a prop of them: a loop
            // that changes the object names its model by the equation.
            if (c.Invariants.IsEmpty)
            {
                var heapParams = string.Concat(regions.Select(k =>
                    $" ({Frontend.Region.HeapBinder(k.Name)}: {Frontend.Region.Module}.heap {RegionRaw(k)})"));
                sb.AppendLine();
                sb.AppendLine($"let {Names.ClassAbsRep(c.Name)}{tb.Implicit} {thisParam}(r: {tb.App(Names.ClassRaw(c.Name))}){heapParams} : prop =");
                sb.AppendLine($"  {SpecEmitter.Conjunction([.. conjuncts.Take(conjuncts.Count - 1).DefaultIfEmpty("True")])}");
                sb.AppendLine();
                sb.AppendLine($"let {Names.ClassAbsModel(c.Name)}{tb.Implicit} {thisParam}(r: {tb.App(Names.ClassRaw(c.Name))}){heapParams} =");
                sb.AppendLine($"  {abstraction}");
            }
        }

        // R27.13. The same invariant with its heaps as indices rather than existentials, so
        // a contract can speak of the region the owner holds, and two conversions between
        // the forms.
        if (!regions.IsEmpty)
        {
            var heapBinders = regions.Select(k =>
                $"({Frontend.Region.HeapBinder(k.Name)}: {Frontend.Region.Module}.heap {RegionRaw(k)})").ToList();
            var heapNames = string.Join(" ", regions.Select(k => Frontend.Region.HeapBinder(k.Name)));
            var invHeap = Names.ClassInvHeap(c.Name);
            var ty = tb.App(Names.ClassType(c.Name));
            var model = tb.App(Names.ClassModel(c.Name));
            sb.AppendLine();
            sb.AppendLine($"let {invHeap}{tb.Implicit} (this: {ty}) (#[T.exact (`1.0R)] p: perm) " +
                          $"(m: {model}) {string.Join(" ", heapBinders)} : slprop =");
            sb.AppendLine($"  exists* {string.Join(" ", existentials.Take(existentials.Count - regions.Length))}.");
            Body();
            sb.AppendLine();
            sb.AppendLine($"ghost fn {Names.ClassToHeap(c.Name)}{tb.Implicit} (this: {ty}) (#p: perm) (#m: {model})");
            sb.AppendLine($"  requires {Names.ClassInv(c.Name)} this #p m");
            sb.AppendLine($"  ensures exists* {heapNames}. {invHeap} this #p m {heapNames}");
            sb.AppendLine("{");
            sb.AppendLine($"  unfold ({Names.ClassInv(c.Name)} this #p m);");
            foreach (var k in regions)
                sb.AppendLine($"  with {Frontend.Region.HeapBinder(k.Name)}. assert ({RegionAt(k, "p", Frontend.Region.HeapBinder(k.Name))});");
            sb.AppendLine($"  fold ({invHeap} this #p m {heapNames})");
            sb.AppendLine("}");
            sb.AppendLine();
            sb.AppendLine($"ghost fn {Names.ClassOfHeap(c.Name)}{tb.Implicit} (this: {ty}) (#p: perm) (#m: {model}) " +
                          string.Join(" ", heapBinders.Select(b => "(#" + b[1..])));
            sb.AppendLine($"  requires {invHeap} this #p m {heapNames}");
            sb.AppendLine($"  ensures {Names.ClassInv(c.Name)} this #p m");
            sb.AppendLine("{");
            sb.AppendLine($"  unfold ({invHeap} this #p m {heapNames});");
            sb.AppendLine($"  fold ({Names.ClassInv(c.Name)} this #p m)");
            sb.AppendLine("}");
        }

        // R27.50. Two objects of the class whose invariants are both held whole are two
        // objects: each owns its box at full permission. Stated of the heap-indexed form
        // when the class owns a region, so that folding back finds each region by its heap.
        if (_compared.Contains(c.Name) && c.BaseClass is null)
        {
            var ty = tb.App(Names.ClassType(c.Name));
            var model = tb.App(Names.ClassModel(c.Name));
            var form = regions.IsEmpty ? Names.ClassInv(c.Name) : Names.ClassInvHeap(c.Name);
            string Heaps(string who) => string.Concat(regions.Select(k => $" {Frontend.Region.HeapBinder(k.Name)}_{who}"));
            var heapBinders = string.Concat(new[] { "x", "y" }.SelectMany(who => regions.Select(k =>
                $" (#{Frontend.Region.HeapBinder(k.Name)}_{who}: {Frontend.Region.Module}.heap {RegionRaw(k)})")));
            var both = $"{form} x m_x{Heaps("x")} ** {form} y m_y{Heaps("y")}";
            sb.AppendLine();
            sb.AppendLine($"ghost fn {Names.ClassDistinct(c.Name)}{tb.Implicit} (x y: {ty}) (#m_x #m_y: {model}){heapBinders}");
            sb.AppendLine($"  requires {both}");
            sb.AppendLine($"  ensures {both} ** pure (~(x == y))");
            sb.AppendLine("{");
            sb.AppendLine($"  unfold ({form} x m_x{Heaps("x")});");
            sb.AppendLine($"  unfold ({form} y m_y{Heaps("y")});");
            sb.AppendLine("  Pulse.Lib.CSharp.Distinct.boxes_distinct x y;");
            sb.AppendLine($"  fold ({form} x m_x{Heaps("x")});");
            sb.AppendLine($"  fold ({form} y m_y{Heaps("y")})");
            sb.AppendLine("}");
        }

        // R27.4. Two halves of an owner hold two heaps that nothing proves equal, so an
        // owner of a region is held whole and has no share or gather.
        // R27.58. So is an owner of one, through the object that holds the heap.
        if (Shareable(c)) EmitShareAndGather(sb, c, arrays, objects);

        // R3.9c: each [Spec] member is a pure function of the model, never of the
        // representation — a caller holds only the model, so an observation it cannot
        // compute from the model is one it cannot use.
        sb.AppendLine();
        _hierarchy.EmitObservations(sb, c);

        // R9.14. A leaf of a hierarchy is an M2 class *and* an implementation of its
        // parent: everything above is emitted unchanged, and what follows is what makes it
        // usable as the parent — the forgetting function, its invariant read at the
        // parent's model, and R3.10d's sharing lifted to that model.
        if (c.BaseClass is { } baseName && _classes.TryGetValue(baseName, out var parent))
        {
            sb.Append(_hierarchy.EmitLeafView(c, parent));
            sb.Append(_hierarchy.EmitLeafShareGather(c, parent));
        }

        return new EmittedModule(Names.ClassModule(c.Name), sb.ToString());
    }

    /// <summary>
    /// R3.10d. The three ghost lemmas that make an object observable through more than one
    /// alias. They are emitted per class, not written once in the support library, because
    /// their proofs recurse into the class's own structure: the box, then each array, then
    /// <em>each sub-object's own</em> <c>share</c> (F22). A generic lemma would have to
    /// quantify over that structure, and there is nothing to quantify over — the invariant
    /// is a <c>let</c>, not an instance of an interface.
    /// <para>
    /// Every <c>fold</c> here is preceded by an <c>assert</c> naming what it consumes. That
    /// is not a proof rescued by the emitter but the scheme itself: after a share the
    /// context holds two candidates for every existential the invariant has, and the
    /// prover solves them by matching. The bodies are fixed by this rule and do not vary
    /// with the program, exactly as R4.10's fold/unfold bracket does not.
    /// </para>
    /// </summary>
    private void EmitShareAndGather(
        StringBuilder sb, IrClass c,
        ImmutableArray<IrFieldDecl> arrays, ImmutableArray<IrFieldDecl> objects)
    {
        var tb = TypeBinders.Of(c);
        var inv = Names.ClassInv(c.Name);
        var ty = tb.App(Names.ClassType(c.Name));
        var model = tb.App(Names.ClassModel(c.Name));
        var half = "(p /. 2.0R)";

        // -- share -----------------------------------------------------------
        sb.AppendLine();
        sb.AppendLine($"ghost fn {Names.ClassInvShare(c.Name)}{tb.Implicit} (this: {ty}) " +
                      $"(#p: perm) (#m: {model})");
        sb.AppendLine($"  requires {inv} this #p m");
        sb.AppendLine($"  ensures {inv} this #{half} m ** {inv} this #{half} m");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({inv} this #p m);");
        sb.AppendLine("  with r. assert (B.pts_to this #p r);");
        foreach (var f in arrays)
            sb.AppendLine($"  with {Names.Contents(f.Name)}. assert " +
                          $"({ArrayPts(f)} r.{Names.Field(f.Name)} #p {Names.Contents(f.Name)});");
        foreach (var f in objects)
            sb.AppendLine($"  with {Names.SubModel(f.Name)}. assert " +
                          $"({SubInvApp(f.Type, $"r.{Names.Field(f.Name)}", "p", Names.SubModel(f.Name))});");
        sb.AppendLine("  B.share this;");
        foreach (var f in arrays)
            sb.AppendLine($"  {ArrayMod(f)}share r.{Names.Field(f.Name)};");
        foreach (var f in objects)
            sb.AppendLine($"  {SubShare(f.Type)} r.{Names.Field(f.Name)};");
        var shared = Resources(c, arrays, objects, half, "r", Names.Contents, Names.SubModel);
        sb.AppendLine($"  assert ({shared});");
        sb.AppendLine($"  fold ({inv} this #{half} m);");
        sb.AppendLine($"  assert ({shared});");
        sb.AppendLine($"  fold ({inv} this #{half} m);");
        sb.AppendLine("}");

        // -- the general gather ---------------------------------------------
        // F23: the models come back *equal*, and that is a consequence rather than an
        // assumption. R3.9 pins `m` to the abstraction function of the representation,
        // `Box.gather` proves the two representations equal, and a function of equal
        // arguments is equal. Two observers of one object cannot disagree about it.
        sb.AppendLine();
        sb.AppendLine("[@@allow_ambiguous]");
        // The two permissions are *explicit*. As implicits they were instantiated by
        // matching, so a nested gather could come back at `q +. p` where its caller's fold
        // wanted `p +. q` — provably the same permission, but slprop matching is syntactic
        // and a user-defined slprop gets no normalisation (F24). Naming them at the call
        // fixes the order once and the whole nesting composes.
        sb.AppendLine($"ghost fn {Names.ClassInvGatherGen(c.Name)}{tb.Implicit} (this: {ty}) " +
                      $"(p q: perm) (#m #alt_m: {model})");
        sb.AppendLine($"  requires {inv} this #p m ** {inv} this #q alt_m");
        sb.AppendLine($"  ensures {inv} this #(p +. q) m ** pure (m == alt_m)");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({inv} this #p m);");
        sb.AppendLine("  with r. assert (B.pts_to this #p r);");
        foreach (var f in arrays)
            sb.AppendLine($"  with {Names.Contents(f.Name)}. assert " +
                          $"({ArrayPts(f)} r.{Names.Field(f.Name)} #p {Names.Contents(f.Name)});");
        foreach (var f in objects)
            sb.AppendLine($"  with {Names.SubModel(f.Name)}. assert " +
                          $"({SubInvApp(f.Type, $"r.{Names.Field(f.Name)}", "p", Names.SubModel(f.Name))});");
        sb.AppendLine($"  unfold ({inv} this #q alt_m);");
        sb.AppendLine("  with alt_r. assert (B.pts_to this #q alt_r);");
        foreach (var f in arrays)
            sb.AppendLine($"  with {Names.Alt(Names.Contents(f.Name))}. assert " +
                          $"({ArrayPts(f)} alt_r.{Names.Field(f.Name)} #q {Names.Alt(Names.Contents(f.Name))});");
        foreach (var f in objects)
            sb.AppendLine($"  with {Names.Alt(Names.SubModel(f.Name))}. assert " +
                          $"({SubInvApp(f.Type, $"alt_r.{Names.Field(f.Name)}", "q", Names.Alt(Names.SubModel(f.Name)))});");
        // The two views are of one object, so the second's resources are renamed onto the
        // first's *before* anything is gathered. The equality has to be learned without
        // consuming either view — hence `pts_to_injective_eq` rather than `gather` — for a
        // reason worth stating: `gather` keeps whichever of the two values it matched
        // first, and slprop matching is syntactic, so a later `fold` looking for the other
        // name would fail against a resource that is provably the same thing. Renaming
        // first leaves exactly one candidate for every existential, and then nothing can
        // be ambiguous.
        sb.AppendLine("  B.pts_to_injective_eq this;");
        sb.AppendLine("  assert (pure (r == alt_r));");
        sb.AppendLine("  rewrite (B.pts_to this #q alt_r) as (B.pts_to this #q r);");
        foreach (var f in arrays)
        {
            var alt = Names.Alt(Names.Contents(f.Name));
            sb.AppendLine($"  rewrite ({ArrayPts(f)} alt_r.{Names.Field(f.Name)} #q {alt})");
            sb.AppendLine($"       as ({ArrayPts(f)} r.{Names.Field(f.Name)} #q {alt});");
        }
        foreach (var f in objects)
        {
            var alt = Names.Alt(Names.SubModel(f.Name));
            sb.AppendLine($"  rewrite ({SubInvApp(f.Type, $"alt_r.{Names.Field(f.Name)}", "q", alt)})");
            sb.AppendLine($"       as ({SubInvApp(f.Type, $"r.{Names.Field(f.Name)}", "q", alt)});");
        }
        sb.AppendLine("  B.gather this;");
        foreach (var f in arrays)
            sb.AppendLine(f.IsNullableArray
                ? $"  NA.gather r.{Names.Field(f.Name)} #{Names.Contents(f.Name)} " +
                  $"#{Names.Alt(Names.Contents(f.Name))} #p #q;"
                : $"  A.gather r.{Names.Field(f.Name)};");
        foreach (var f in objects)
            sb.AppendLine($"  {SubGatherGen(f.Type)} r.{Names.Field(f.Name)} p q;");
        // No `assert` before this `fold`, unlike `share`'s: one candidate per existential
        // is left, so there is nothing to disambiguate, and the abstraction equation is
        // discharged by SMT from the `pure (… == …)` each gather returned.
        sb.AppendLine($"  fold ({inv} this #(p +. q) m);");
        sb.AppendLine("}");

        // -- gather, stated as share's exact inverse -------------------------
        // F24: Pulse normalises `p /. 2.0R +. p /. 2.0R` for `pts_to`, which has prover
        // support, but not for a user-defined slprop, which is matched syntactically.
        // Discharging the arithmetic here is what keeps it out of every call site, where
        // it would be a proof step about the encoding rather than about the program.
        sb.AppendLine();
        sb.AppendLine("[@@allow_ambiguous]");
        sb.AppendLine($"ghost fn {Names.ClassInvGather(c.Name)}{tb.Implicit} (this: {ty}) " +
                      $"(#p: perm) (#m #alt_m: {model})");
        sb.AppendLine($"  requires {inv} this #{half} m ** {inv} this #{half} alt_m");
        sb.AppendLine($"  ensures {inv} this #p m ** pure (m == alt_m)");
        sb.AppendLine("{");
        sb.AppendLine($"  {Names.ClassInvGatherGen(c.Name)} this {half} {half};");
        sb.AppendLine($"  rewrite ({inv} this #(p /. 2.0R +. p /. 2.0R) m) as ({inv} this #p m);");
        sb.AppendLine("}");
    }

    /// <summary>
    /// R3.10d. Every resource the invariant holds, at one permission — what the
    /// <c>assert</c> before a <c>fold</c> has to name so the prover can solve the
    /// invariant's existentials against a context that holds two candidates for each.
    /// </summary>
    /// <summary>R24.7. The resource an array field is owned through.</summary>
    public static string ArrayPts(IrFieldDecl f) => f.IsNullableArray ? "NA.pts_to" : "A.pts_to";

    /// <summary>R24.7. The module whose <c>share</c>/<c>gather</c> an array field uses.</summary>
    public static string ArrayMod(IrFieldDecl f) => f.IsNullableArray ? "NA." : "A.";

    private static string Resources(
        IrClass c, ImmutableArray<IrFieldDecl> arrays, ImmutableArray<IrFieldDecl> objects,
        string perm, string record, Func<string, string> contents, Func<string, string> submodel)
    {
        var parts = new List<string> { $"B.pts_to this #{perm} {record}" };
        parts.AddRange(arrays.Select(f =>
            $"{ArrayPts(f)} {record}.{Names.Field(f.Name)} #{perm} {contents(f.Name)}"));
        parts.AddRange(objects.Select(f =>
            SubInvApp(f.Type, $"{record}.{Names.Field(f.Name)}", perm, submodel(f.Name))));
        return string.Join(" ** ", parts);
    }

    // =======================================================================
    // Methods (R4.1)
    // =======================================================================

    private EmittedModule EmitMethod(IrMethod method)
    {
        var held = _regionHeld.TryGetValue(method.Name, out var hr) ? hr : [];
        var body = new CodeEmitter(_spec, diagnostics, _classes, _overrides, _slots, _consumed, _heapIndexed, _regionHeld,
            _openMethods, _raising, _readOnly);
        var plan = new MethodPlan(method, _spec, diagnostics,
            _heapIndexed.TryGetValue(method.Name, out var heaps) ? heaps : [], held,
            method.Open && method.DeclaringClass is { } oc && _classes.TryGetValue(oc, out var openClass)
                ? openClass.Fields : default,
            method.ReturnType is IrNamedType rn && _ownedFields.TryGetValue(rn.Name, out var ro) ? ro : default,
            _heapsKept.Contains(method.Name), _methods);

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.FunctionModule(method.Name)}");
        sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        var methodOpens = Dependencies(
            Names.FunctionModule(method.Name), method.Body,
            method.Requires, method.Ensures, method.Preserves,
            method.Throws.Where(t => t.When is not null).Select(t => t.When!));
        var classOpens = method.Parameters
            .Select(p => p.Type is IrClassType ct && _classes.TryGetValue(ct.Name, out var owner) ? owner : null)
            .OfType<IrClass>()
            .SelectMany(ClassSpecOpens);
        foreach (var open in methodOpens.Union(classOpens).Distinct())
            sb.AppendLine($"open {open}");
        sb.AppendLine(Preamble.Opens);
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        if (method.RlimitFactor is { } factor)
        {
            sb.AppendLine($"#set-options \"--z3rlimit_factor {factor}\"");
            sb.AppendLine();
        }

        var origins = ImmutableArray.CreateBuilder<LineOrigin>();

        origins.Add(new LineOrigin(Lines(sb) + 1, method.Loc));
        sb.Append(_recursiveMethod ? "fn rec " : "fn ").Append(Names.Function(method.Name));
        foreach (var b in plan.Binders) sb.Append(' ').Append(b);
        sb.AppendLine();

        // The contract lines get their own origins, and they are the ones that pay: an
        // unproved postcondition is reported by F* against the `ensures` of the generated
        // `fn`, which is a line the user did not write. Pointing it at the `[Ensures]`
        // they did write is the whole difference between a usable message and a puzzle.
        origins.Add(new LineOrigin(Lines(sb) + 1, Clause(method.Requires) ?? method.Loc));
        sb.AppendLine($"  requires {plan.Requires}");
        if (method.ReturnType is not IrPrim { Kind: PrimKind.Void })
            sb.AppendLine($"  returns  {Names.Result}: {Types.Render(method.ReturnType)}");
        origins.Add(new LineOrigin(Lines(sb) + 1, Clause(method.Ensures) ?? method.Loc));
        sb.AppendLine($"  ensures  {plan.Ensures}");
        if (plan.Raises is { } raises)
        {
            origins.Add(new LineOrigin(Lines(sb) + 1, method.Throws[0].Loc));
            sb.AppendLine($"  raises   {raises}");
        }

        // R10.6/F2. A `fn rec` needs a measure for the same reason a `while` does: without
        // one it is `stt_div` and will not compose with its `stt` continuation. Guessing
        // one would be the emitter inventing a proof step, so it is the user's
        // `[Decreases]` or nothing — and nothing is refused by Check.
        if (method.Decreases is { } measure)
        {
            origins.Add(new LineOrigin(Lines(sb) + 1, measure.Loc));
            sb.AppendLine($"  decreases {_spec.Emit(measure, plan.PreScope).Text}");
        }
        origins.Add(new LineOrigin(Lines(sb) + 1, method.Loc));
        sb.AppendLine("{");

        if (method.Admit)
        {
            sb.AppendLine("  admit()");
        }
        else if (method.PulseBody is { } raw)
        {
            // Raw Pulse is the user's own text, so every line of it is theirs. There is
            // no finer answer available: the block is opaque to the translator by
            // construction (R4.8).
            foreach (var line in Antiquotation.Expand(raw, plan.PreScope).Split('\n'))
            {
                origins.Add(new LineOrigin(Lines(sb) + 1, method.Loc));
                sb.AppendLine("  " + line.TrimEnd());
            }
        }
        else if (method.Body is not null)
        {
            var offset = Lines(sb);
            sb.Append(body.EmitBody(method, plan));
            foreach (var o in body.Origins())
                origins.Add(o with { Line = o.Line + offset });
        }

        sb.AppendLine("}");
        if (method.Lambda is { } lambda) EmitLambdaWrapper(sb, method, lambda, plan);

        return new EmittedModule(Names.FunctionModule(method.Name), sb.ToString())
        {
            Origins = origins.ToImmutable(),
        };
    }

    /// <summary>
    /// R27.39. A lifted lambda's protocol and callback. The protocol at a trace owns what the
    /// lambda captures, at values its protocol clause holds of; the callback is the lambda
    /// at the type of a <c>[Callback]</c> parameter, opening the protocol around one call.
    /// </summary>
    private void EmitLambdaWrapper(StringBuilder sb, IrMethod method, IrLambdaInfo lambda, MethodPlan plan)
    {
        static string BinderName(string b) =>
            System.Text.RegularExpressions.Regex.Match(b, @"^[\(\{]\|?\s*#?([^:\s]+)").Groups[1].Value;
        var tyCount = method.TypeParameters.Length + method.DefaultedTypeParameters.Length;
        var tys = plan.ParamBinders.Take(tyCount).ToList();
        var tyNames = tys.Select(BinderName).Where(n => n != "_").ToList();
        var own = plan.ParamBinders.Skip(tyCount).ToList();
        // The trace leads and the node closes the lifted method's parameters.
        var traceBinder = own[0];
        var captures = own.Skip(1).Take(own.Count - 2).ToList();
        var captureNames = captures.Select(BinderName).ToList();
        var ghosts = new List<string>();
        foreach (var p in method.Parameters.Skip(1).Take(method.Parameters.Length - 2))
        {
            if (p.IsGhost) continue;
            switch (p.Type)
            {
                case IrArrayType a: ghosts.Add($"(pre_{p.Name}: erased (Seq.seq {Types.Atom(a.Element)}))"); break;
                case IrSpanType sp: ghosts.Add($"(pre_{p.Name}: erased (Seq.seq {Types.Atom(sp.Element)}))"); break;
                case var t when p.Mode is ParamMode.Ref:
                    ghosts.Add($"(pre_{p.Name}: erased ({Types.Render(t)}))"); break;
                // R27.40. A captured object is owned at its model, like an array at its contents.
                case IrClassType { Plain: false } c when p.Fraction is null && !c.Nullable:
                    ghosts.Add($"(pre_{p.Name}: erased ({Types.Applied($"{Names.ClassModule(c.Name)}.{Names.ClassModel(c.Name)}", c.TypeArguments)}))");
                    break;
                case IrClassType { Plain: false }:
                    diagnostics.Error("PALCS0709", p.Loc,
                        $"A lambda passed to a `[Callback]` parameter captures the object `{p.Name}` " +
                        "(doc/translation.md R27.39–R27.40): a captured object must be non-null and owned in full.");
                    break;
            }
        }
        var cb = lambda.Callback;
        var entry = Types.Atom(new IrUserSpecType("ValueTuple", Frontend.WellKnown.TupleType, [cb.View, cb.Result]));
        var raw = RegionRaw(cb.Region);
        var view = $"{Names.ClassModule(cb.Region.Name)}.{Frontend.Region.ViewOf(cb.Region.Name)}";
        var traceName = BinderName(traceBinder);
        var protocol = Names.LambdaProtocol(method.Name);
        var applied = string.Join(" ", tyNames.Concat(captureNames));
        string P(string trace) => $"({protocol} {applied} {trace})".Replace("  ", " ");
        // The lifted method requires its protocol, then the call bound, then the node's membership.
        var conjuncts = plan.PreConjuncts.Take(plan.PreConjuncts.Length - 2).Where(c => c.Length > 0).ToList();
        var parts = plan.ParamPreResources.Where(r => r.Length > 0).ToList();
        if (conjuncts.Count > 0) parts.Add($"pure ({SpecEmitter.Conjunction([.. conjuncts])})");
        if (parts.Count == 0) parts.Add("emp");

        sb.AppendLine();
        sb.Append($"let {protocol}");
        foreach (var b in tys.Where(b => !b.StartsWith("{|"))) sb.Append(' ').Append(b);
        foreach (var b in captures) sb.Append(' ').Append(b);
        sb.AppendLine($" (tr_raw: Seq.seq {entry}) : slprop =");
        sb.AppendLine($"  let {traceName} : erased (Seq.seq {entry}) = hide tr_raw in");
        sb.AppendLine(ghosts.Count > 0
            ? $"  exists* {string.Join(" ", ghosts)}. {string.Join(" ** ", parts)}"
            : $"  {string.Join(" ** ", parts)}");
        sb.AppendLine();

        sb.Append($"fn {Names.LambdaCallback(method.Name)}");
        foreach (var b in tys) sb.Append(' ').Append(b);
        foreach (var b in captures) sb.Append(' ').Append(b);
        sb.AppendLine($" (#tr: erased (Seq.seq {entry})) (#q: perm) (#h: erased ({Frontend.Region.Module}.heap {raw}))");
        sb.AppendLine($"  (x: B.box {raw} {{ not (B.is_null x) /\\ {Frontend.Region.Module}.mem h x }})");
        var after = $"(Seq.snoc (reveal tr) ({view} x ({Frontend.Region.Module}.get h x), r))";
        sb.AppendLine($"  requires {P("(reveal tr)")} ** {Frontend.Region.Module}.region #{raw} #q h ** " +
                      "pure (Seq.length (reveal tr) < Pulse.Lib.CSharp.Callback.max_calls)");
        sb.AppendLine($"  returns r: {Types.Render(cb.Result)}");
        sb.AppendLine($"  ensures {P(after)} ** {Frontend.Region.Module}.region #{raw} #q h");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold {P("(reveal tr)")};");
        sb.AppendLine($"  let r = {Names.Function(method.Name)} {string.Join(" ", tyNames.Append("tr").Concat(captureNames).Append("x"))};");
        sb.AppendLine($"  fold {P(after)};");
        sb.AppendLine("  r");
        sb.AppendLine("}");
    }

    /// <summary>
    /// How many complete lines the module text holds so far, so that the next
    /// <c>AppendLine</c> can be numbered before it is written.
    /// </summary>
    private static int Lines(StringBuilder sb)
    {
        var n = 0;
        for (var i = 0; i < sb.Length; i++) if (sb[i] == '\n') n++;
        return n;
    }

    /// <summary>The span of a contract, which is the first clause the user wrote of it.</summary>
    private static IrLoc? Clause(ImmutableArray<IrExpr> clauses) =>
        clauses.IsDefaultOrEmpty ? null : clauses[0].Loc;

    /// <summary>
    /// Modules this declaration's translation must <c>open</c>: one per <c>[Spec]</c>
    /// function, <c>[Lemma]</c> or method it mentions, anywhere — including inside a
    /// loop invariant, which is easy to forget and produces an "identifier not found"
    /// only once F* runs.
    /// </summary>
    /// <summary>
    /// R9.12. The abstract class a call dispatches through, if any. A call whose resolved
    /// target is <c>Shape.GetArea</c> is a virtual call however the receiver was written,
    /// and goes to the wrapper in <c>Class_Shape</c> rather than to a <c>Func_</c> module
    /// that does not exist — an abstract method has no body to put in one.
    /// </summary>
    public static string? DispatchOwner(
        IReadOnlyDictionary<string, IrClass>? classes, HashSet<string>? slots, string callee) =>
        slots is null || !slots.Contains(callee)
            ? null
            : classes?.Values
                .FirstOrDefault(c => c.IsAbstract &&
                                     callee.StartsWith(c.Name + "_", StringComparison.Ordinal))
                ?.Name;

    /// <summary>
    /// R9.18. Whose dispatching wrapper a virtual call goes to: the class the receiver is
    /// <em>statically</em> typed at, which at depth three need not be the class that
    /// declared the method.
    ///
    /// <para>The two differ for an inherited virtual called through an intermediate class,
    /// and the difference is not cosmetic: a wrapper's contract and invariant are written
    /// at its own class's model, so <c>q.GetArea()</c> on a <c>Quadrilateral</c> must go to
    /// <c>Quadrilateral</c>'s wrapper — <c>Shape</c>'s would demand a <c>Shape</c>
    /// invariant the caller does not hold. The <em>slot</em> reached is the same one either
    /// way, which is why the method still keeps the name it was declared with (R9.18).</para>
    /// </summary>
    public static string? DispatchClass(
        IReadOnlyDictionary<string, IrClass>? classes, HashSet<string>? slots, IrCall call)
    {
        if (DispatchOwner(classes, slots, call.Callee) is not { } declared) return null;
        return call.HasReceiver && call.Args.Length > 0 &&
               call.Args[0].Type is IrClassType receiver && classes is not null &&
               classes.TryGetValue(receiver.Name, out var k) && k.IsAbstract
            ? receiver.Name
            : declared;
    }

    /// <summary>
    /// R24.17. The `[Spec]` function modules a class's invariant, model and observations
    /// name: the class module opens them, and so does every method of the class, whose
    /// unfoldings of the invariant mention them.
    /// </summary>
    private IEnumerable<string> ClassSpecOpens(IrClass c)
    {
        var saved = _recursiveMethod;
        var opens = Dependencies(Names.ClassModule(c.Name), null,
                c.Invariants, c.ModelRefinements, c.ModelBody is { } mb ? [mb] : [],
                c.Observations.Select(o => o.Body))
            .Where(o => o.StartsWith(Names.SpecModule(""), StringComparison.Ordinal))
            .ToImmutableArray();
        _recursiveMethod = saved;
        return opens;
    }

    private ImmutableArray<string> Dependencies(
        string self, IrStmt? body, params IEnumerable<IrExpr>[] specifications)
    {
        var names = new HashSet<string>();
        Collect(body);
        foreach (var group in specifications)
            foreach (var e in group) CollectExpr(e);

        void Collect(IrStmt? s)
        {
            switch (s)
            {
                case null: return;
                case IrBlock b: foreach (var x in b.Statements) Collect(x); return;
                case IrLocalDecl d: CollectExpr(d.Init); return;
                case IrAssign a: CollectExpr(a.Target); CollectExpr(a.Value); return;
                case IrIf i: CollectExpr(i.Cond); Collect(i.Then); Collect(i.Else); return;
                case IrWhile w:
                    CollectExpr(w.Cond);
                    foreach (var inv in w.Invariants) CollectExpr(inv);
                    Collect(w.Body);
                    return;
                case IrReturn r: CollectExpr(r.Value); return;
                case IrThrow th: CollectExpr(th.Value); return;
                case IrTry tr:
                    foreach (var inv in tr.Invariants) CollectExpr(inv);
                    Collect(tr.Body);
                    foreach (var c in tr.Catches) { CollectExpr(c.When); Collect(c.Body); }
                    return;
                case IrExprStmt e: CollectExpr(e.Expr); return;
                case IrArrayOp c: foreach (var a in c.Args) CollectExpr(a); return;
                case IrGhostStmt g: CollectExpr(g.Prop); return;
                default: return;
            }
        }

        void CollectExpr(IrExpr? e)
        {
            switch (e)
            {
                case null: return;
                case IrCall { Kind: CalleeKind.Callback } cb:
                    foreach (var a in cb.Args) CollectExpr(a);
                    return;
                case IrLambdaRef lr:
                    names.Add(Names.FunctionModule(lr.Method));
                    foreach (var a in lr.Captures) CollectExpr(a);
                    return;
                case IrCall c:
                    names.Add(c.Kind is CalleeKind.Spec or CalleeKind.Lemma
                        ? Names.SpecModule(c.Callee)
                        : DispatchClass(_classes, _slots, c) is { } owner
                            ? Names.ClassModule(owner)
                            : Names.FunctionModule(c.Callee));
                    foreach (var a in c.Args) CollectExpr(a);
                    return;
                case IrBinary b: CollectExpr(b.Left); CollectExpr(b.Right); return;
                case IrUnary u: CollectExpr(u.Operand); return;
                case IrConditional t: CollectExpr(t.Cond); CollectExpr(t.Then); CollectExpr(t.Else); return;
                case IrElement el: CollectExpr(el.Array); CollectExpr(el.Index); return;
                case IrLength l: CollectExpr(l.Array); return;
                case IrOld o: CollectExpr(o.Operand); return;
                case IrNewArray na: CollectExpr(na.Length); if (na.Source is { } nas) CollectExpr(nas); return;
                case IrArraySearch se: CollectExpr(se.Array); CollectExpr(se.Item); CollectExpr(se.Start); CollectExpr(se.Count); return;
                case IrArrayBinarySearch bs: CollectExpr(bs.Array); CollectExpr(bs.Start); CollectExpr(bs.Count); CollectExpr(bs.Item); CollectExpr(bs.Comparer); return;
                case IrNewException ne: foreach (var a in ne.Args) CollectExpr(a); return;
                case IrField f: CollectExpr(f.Receiver); return;
                case IrContents ct: CollectExpr(ct.Array); return;
                case IrSeqOp s: foreach (var a in s.Args) CollectExpr(a); return;
                case IrListOp l2: foreach (var a in l2.Args) CollectExpr(a); return;
                case IrSpecOp so: foreach (var a in so.Args) CollectExpr(a); return;
                case IrObserve ob: CollectExpr(ob.Receiver); return;
                case IrQuantifier q: CollectExpr(q.Body); return;
                case IrConvert cv: CollectExpr(cv.Operand); return;
                case IrStmtExpr se: foreach (var s in se.Prelude) Collect(s); CollectExpr(se.Value); return;
                case IrOptionOp oo: CollectExpr(oo.Operand); return;
                case IrRaise ra: CollectExpr(ra.Exception); return;
                case IrNew nw: foreach (var fi in nw.Fields) CollectExpr(fi.Value); return;
                default: return;
            }
        }

        // R10.6. A method that names itself is a Pulse `fn rec`. The dependency scan
        // already had to answer this question, so asking it here costs nothing and keeps
        // one walker rather than two.
        _recursiveMethod = names.Remove(self);
        return [.. names.OrderBy(n => n, StringComparer.Ordinal)];
    }

}

/// <summary>The fixed header every generated module carries.</summary>
public static class Preamble
{
    public const string Opens =
        """
        open Pulse
        open Pulse.Lib.CSharp.Array
        open Pulse.Lib.CSharp.Casts
        """;

    public const string Modules =
        """
        module R = Pulse.Lib.Reference
        module A = Pulse.Lib.Array
        module S = Pulse.Lib.Slice
        module Span = Pulse.Lib.CSharp.Span
        module B = Pulse.Lib.Box
        module I8 = FStar.Int8
        module I16 = FStar.Int16
        module I32 = FStar.Int32
        module I64 = FStar.Int64
        module U8 = FStar.UInt8
        module U16 = FStar.UInt16
        module U32 = FStar.UInt32
        module U64 = FStar.UInt64
        module Seq = FStar.Seq
        module CS = Pulse.Lib.CSharp.Seq
        module CA = Pulse.Lib.CSharp.Arith
        module CL = Pulse.Lib.CSharp.List
        module List = FStar.List.Tot
        module Cast = FStar.Int.Cast
        module D = Pulse.Lib.CSharp.Decimal
        module Linq = Pulse.Lib.CSharp.Linq
        module Opaque = Pulse.Lib.CSharp.Opaque
        module NA = Pulse.Lib.CSharp.NullableArray
        """;
}

/// <summary>R27.16. A region a method holds itself, and whether it writes it.</summary>
public sealed record RegionUse(IrClassType Region, bool Mutates);
