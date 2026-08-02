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

    /// <summary>For an object slot: the ghost binder holding its model on entry.</summary>
    public string? PreModel { get; init; }

    /// <summary>
    /// For an object slot: the binder its invariant is re-folded at on exit. Equal to
    /// <see cref="PreModel"/> for a read-only method (R4.11a).
    /// </summary>
    public string? PostModel { get; init; }

    /// <summary>The resource conjunct owning this slot, given a value binder.</summary>
    public string Resource(string value) => Kind switch
    {
        SlotKind.Cell => $"R.pts_to {Binder} {value}",
        SlotKind.RefParam => $"R.pts_to {Binder} {Perm}{value}",
        SlotKind.Array => $"A.pts_to {Binder} {Perm}{value}",
        SlotKind.Object when Type is IrClassType c =>
            $"{Names.ClassModule(c.Name)}.{Names.ClassInv(c.Name)} {Binder} {Perm}{value}",
        _ => "",
    };

    public bool Owns => Kind is SlotKind.Cell or SlotKind.RefParam or SlotKind.Array or SlotKind.Object;
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
    /// <summary>
    /// An object: a <c>B.box</c> of the class's representation, owned through
    /// <c>class_C__inv</c> rather than a <c>pts_to</c> (R3.8, R4.10).
    /// </summary>
    Object,
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

    public ImmutableArray<EmittedModule> Emit(IrProgram program)
    {
        var modules = ImmutableArray.CreateBuilder<EmittedModule>();
        _classes = program.Declarations.OfType<IrClass>().ToDictionary(c => c.Name);
        foreach (var decl in program.Declarations)
        {
            var module = decl switch
            {
                IrSpecFunction s => EmitSpecFunction(s),
                IrMethod { IsLemma: true } m => EmitLemma(m),
                IrMethod m => EmitMethod(m),
                IrStruct s => EmitStruct(s),
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
                    .. cl.Observations.Select(o =>
                        new Provenance(Names.Observation(cl.Name, o.Name), o.Loc)),
                ],
                _ => [new Provenance(construct, decl.Loc)],
            };

            modules.Add(module with { Origin = origin });
        }
        return modules.ToImmutable();
    }

    // =======================================================================
    // [Spec] functions (R4.6)
    // =======================================================================

    private EmittedModule EmitSpecFunction(IrSpecFunction fn)
    {
        var scope = new SpecScope();
        var binders = new List<string>();

        foreach (var p in fn.Parameters)
        {
            var name = Names.Local(p.Name);
            switch (p.Type)
            {
                case IrArrayType a:
                    binders.Add($"({name}: Seq.seq {Types.Render(a.Element)})");
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
        if (fn.Requires.Length > 0 && binders.Count > 0)
        {
            var refinement = SpecEmitter.Conjunction(fn.Requires.Select(r => _spec.AsProp(_spec.Emit(r, scope))));
            var last = binders[^1];
            binders[^1] = last[..^1] + " { " + refinement + " })";
        }

        var (returnType, text) = fn.ReturnType switch
        {
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

        foreach (var p in lemma.Parameters)
        {
            var name = Names.Local(p.Name);
            var (rendered, kind) = p.Type switch
            {
                IrArrayType a => ($"Seq.seq {Types.Render(a.Element)}", TermKind.Seq),
                IrSeqType s => ($"Seq.seq {Types.Render(s.Element)}", TermKind.Seq),
                IrGhostType g => (Types.Render(g.Inner), MethodPlan.KindOf(g.Inner)),
                _ => (Types.Render(p.Type), MethodPlan.KindOf(p.Type)),
            };
            binders.Add($"({name}: {rendered})");
            scope.Bind(p.Name, new Term(name, kind, p.Type));
        }

        var requires = SpecEmitter.Conjunction(lemma.Requires.Select(r => _spec.AsProp(_spec.Emit(r, scope))));
        var ensures = SpecEmitter.Conjunction(
            lemma.Ensures.Concat(lemma.Preserves).Select(e => _spec.AsProp(_spec.Emit(e, scope))));

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.SpecModule(lemma.Name)}");
        sb.AppendLine();
        foreach (var open in Dependencies(
                     Names.SpecModule(lemma.Name), null, lemma.Requires, lemma.Ensures, lemma.Preserves))
            sb.AppendLine($"open {open}");
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        sb.Append("let ").Append(Names.Lemma(lemma.Name));
        foreach (var b in binders) sb.Append(' ').Append(b);
        sb.AppendLine();
        sb.AppendLine($"  : Lemma (requires ({requires}))");
        sb.AppendLine($"          (ensures ({ensures}))");

        var body = lemma switch
        {
            { Admit: true } => "admit()",
            { PulseBody: { } raw } => Antiquotation.Expand(raw, scope),
            _ => "()",
        };
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
        sb.Append("noeq type ").Append(Names.StructRaw(s.Name)).AppendLine(" = {");
        foreach (var f in s.Fields)
            sb.AppendLine($"  {Names.Field(f.Name)}: {Types.Render(f.Type)};");
        sb.AppendLine("}");
        sb.AppendLine();
        // The refinement predicate is emitted even when trivial: uniform output beats
        // output whose shape depends on whether the user happened to write [Refine].
        sb.AppendLine($"let {Names.StructPred(s.Name)} (this: {Names.StructRaw(s.Name)}) : prop =");
        sb.AppendLine($"  {predicate}");
        sb.AppendLine();
        sb.AppendLine($"type {Names.StructType(s.Name)} = " +
                      $"this: {Names.StructRaw(s.Name)} {{ {Names.StructPred(s.Name)} this }}");

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

    /// <summary>R3.10b. The sub-object's model type, qualified by its own module.</summary>
    internal static string SubModelType(IrType t) =>
        $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassModel(((IrClassType)t).Name)}";

    /// <summary>R3.10d. A sub-object's own <c>share</c>, qualified by its module.</summary>
    private static string SubShare(IrType t) =>
        $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassInvShare(((IrClassType)t).Name)}";

    /// <summary>R3.10d. A sub-object's general <c>gather</c>, qualified by its module.</summary>
    private static string SubGatherGen(IrType t) =>
        $"{Names.ClassModule(((IrClassType)t).Name)}.{Names.ClassInvGatherGen(((IrClassType)t).Name)}";

    private EmittedModule EmitClass(IrClass c)
    {
        // R3.7: inside the defining module a field needs no qualifier, and must not have
        // one, or F*'s dependency scan reads the module as depending on itself.
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
                IrArrayType => new Term(Names.Contents(f.Name), TermKind.Seq, f.Type),
                IrClassType => new Term(Names.SubModel(f.Name), TermKind.Math, f.Type),
                _ => new Term($"r.{Names.Field(f.Name)}", MethodPlan.KindOf(f.Type), f.Type),
            };
            repScope.Bind(f.Name, term);
        }
        var arrays = c.Fields.Where(f => f.Type is IrArrayType).ToImmutableArray();
        var objects = c.Fields.Where(f => f.Type is IrClassType).ToImmutableArray();

        // R3.9d: the model refinement is stated over the model value, which a [Refine]
        // on the [Model] member names `Result`, as an [Ensures] does.
        var modelKind = MethodPlan.KindOf(c.ModelType);
        var modelScope = new SpecScope { ResultTerm = "m", ResultKind = modelKind };
        var modelPred = c.ModelRefinements.Length == 0
            ? "True"
            : SpecEmitter.Conjunction(
                c.ModelRefinements.Select(r => _spec.AsProp(_spec.Emit(r, modelScope))));

        // R3.9b: the [Invariant] clauses and the abstraction relation are conjuncts of one
        // `pure`, and the order is load-bearing. `p1 /\ p2` types `p2` with `p1` in scope,
        // so the [Invariant] clauses come *first*: they are the bounds that make a partial
        // abstraction such as `Seq.slice contents 0 top` well-typed where it appears.
        // The equation is stated at the model's kind: a `SpecInt` model of an `int` field
        // is that field's mathematical value, so the abstraction carries the `Int32.v` that
        // §6 puts on every integer in spec position.
        var abstraction = modelKind == TermKind.Math
            ? _spec.Math(c.ModelBody, repScope)
            : _spec.Emit(c.ModelBody, repScope).Text;
        var conjuncts = new List<string>();
        // R3.10a. A C# array's length is an `int`, so this bound is a fact about the
        // source type and not an assumption: it enters at `new T[n]`, whose length
        // argument is already an `int`, and rides round every fold from there. It is
        // stated first because it is what makes arithmetic on an index into the array
        // provably non-overflowing.
        foreach (var f in arrays)
            conjuncts.Add($"Seq.length {Names.Contents(f.Name)} <= 2147483647");
        conjuncts.AddRange(c.Invariants.Select(i => _spec.AsProp(_spec.Emit(i, repScope))));
        conjuncts.Add($"m == {abstraction}");

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.ClassModule(c.Name)}");
        sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        sb.AppendLine(Preamble.Opens);
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();

        // R3.10c needs `T.exact` for the invariant's defaulted permission binder. The
        // alias is emitted here rather than in the shared preamble because a class module
        // is the only one that has a use for it.
        sb.AppendLine("module T = FStar.Tactics");
        sb.AppendLine();

        sb.Append("noeq type ").Append(Names.ClassRaw(c.Name)).AppendLine(" = {");
        foreach (var f in c.Fields)
            sb.AppendLine($"  {Names.Field(f.Name)}: {Types.Render(f.Type)};");
        sb.AppendLine("}");
        sb.AppendLine();

        // R3.8: a CLR object reference is a `Box.box` of the representation. `Box` is the
        // sound heap cell (F14); `Reference.alloc` is marked unsound and never emitted.
        sb.AppendLine($"let {Names.ClassType(c.Name)} = B.box {Names.ClassRaw(c.Name)}");
        sb.AppendLine();

        // R3.9d. Emitted even when the predicate is `True`, for the same reason
        // `struct_S__pred` is (§0 rule 2): uniform output beats output whose shape
        // depends on whether the user happened to write [Refine].
        var modelType = Types.Render(c.ModelType);
        sb.AppendLine($"let {Names.ClassModelPred(c.Name)} (m: {modelType}) : prop =");
        sb.AppendLine($"  {modelPred}");
        sb.AppendLine();
        sb.AppendLine($"type {Names.ClassModel(c.Name)} = " +
                      $"m: {modelType} {{ {Names.ClassModelPred(c.Name)} m }}");
        sb.AppendLine();

        // R3.10: the invariant is indexed by the model. An un-indexed `inv (x: C)` puts
        // the object's whole state under an existential, so no postcondition could relate
        // the post-state to the pre-state — memory safety and nothing more.
        //
        // R3.10c: it is also indexed by a *permission*, which propagates to every resource
        // conjunct. The binder is meta-argument-defaulted (F21), so `class_C__inv x m`
        // still means full ownership and no other rule's output changes: the whole feature
        // is reached by asking for it.
        sb.AppendLine($"let {Names.ClassInv(c.Name)} (this: {Names.ClassType(c.Name)}) " +
                      $"(#[T.exact (`1.0R)] p: perm) (m: {Names.ClassModel(c.Name)}) : slprop =");
        var existentials = new List<string> { $"(r: {Names.ClassRaw(c.Name)})" };
        existentials.AddRange(arrays.Select(f =>
            $"({Names.Contents(f.Name)}: Seq.seq {Types.Render(((IrArrayType)f.Type).Element)})"));
        existentials.AddRange(objects.Select(f =>
            $"({Names.SubModel(f.Name)}: {SubModelType(f.Type)})"));
        sb.AppendLine($"  exists* {string.Join(" ", existentials)}.");
        sb.AppendLine("    B.pts_to this #p r **");
        foreach (var f in arrays)
            sb.AppendLine($"    A.pts_to r.{Names.Field(f.Name)} #p {Names.Contents(f.Name)} **");
        // R3.10b. The sub-object's own invariant, at its own model. Nesting is one
        // conjunct: the outer invariant does not restate the inner one, it *contains* it,
        // so an inner class's [Invariant] clauses are proved once, where they were written.
        // R3.10c hands it the *same* fraction: an object held at `p` is one every part of
        // which is held at `p`, and there is no other coherent reading.
        foreach (var f in objects)
            sb.AppendLine($"    {SubInv(f.Type)} r.{Names.Field(f.Name)} #p {Names.SubModel(f.Name)} **");
        sb.AppendLine($"    pure ({SpecEmitter.Conjunction(conjuncts)})");

        EmitShareAndGather(sb, c, arrays, objects);

        // R3.9c: each [Spec] member is a pure function of the model, never of the
        // representation — a caller holds only the model, so an observation it cannot
        // compute from the model is one it cannot use.
        foreach (var o in c.Observations)
        {
            var obsScope = new SpecScope();
            obsScope.Bind(c.ModelMember, new Term("m", modelKind, c.ModelType));
            var (ret, text) = o.ReturnType switch
            {
                IrPrim { Kind: PrimKind.Bool } => ("prop", _spec.AsProp(_spec.Emit(o.Body, obsScope))),
                IrPrim { IsMachineInt: true } => ("int", _spec.Math(o.Body, obsScope)),
                _ => (Types.Render(o.ReturnType), _spec.Emit(o.Body, obsScope).Text),
            };
            sb.AppendLine();
            sb.AppendLine($"let {Names.Observation(c.Name, o.Name)} " +
                          $"(m: {Names.ClassModel(c.Name)}) : {ret} =");
            sb.AppendLine($"  {text}");
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
        var inv = Names.ClassInv(c.Name);
        var ty = Names.ClassType(c.Name);
        var model = Names.ClassModel(c.Name);
        var half = "(p /. 2.0R)";

        // -- share -----------------------------------------------------------
        sb.AppendLine();
        sb.AppendLine($"ghost fn {Names.ClassInvShare(c.Name)} (this: {ty}) " +
                      $"(#p: perm) (#m: {model})");
        sb.AppendLine($"  requires {inv} this #p m");
        sb.AppendLine($"  ensures {inv} this #{half} m ** {inv} this #{half} m");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({inv} this #p m);");
        sb.AppendLine("  with r. assert (B.pts_to this #p r);");
        foreach (var f in arrays)
            sb.AppendLine($"  with {Names.Contents(f.Name)}. assert " +
                          $"(A.pts_to r.{Names.Field(f.Name)} #p {Names.Contents(f.Name)});");
        foreach (var f in objects)
            sb.AppendLine($"  with {Names.SubModel(f.Name)}. assert " +
                          $"({SubInv(f.Type)} r.{Names.Field(f.Name)} #p {Names.SubModel(f.Name)});");
        sb.AppendLine("  B.share this;");
        foreach (var f in arrays)
            sb.AppendLine($"  A.share r.{Names.Field(f.Name)};");
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
        sb.AppendLine($"ghost fn {Names.ClassInvGatherGen(c.Name)} (this: {ty}) " +
                      $"(p q: perm) (#m #alt_m: {model})");
        sb.AppendLine($"  requires {inv} this #p m ** {inv} this #q alt_m");
        sb.AppendLine($"  ensures {inv} this #(p +. q) m ** pure (m == alt_m)");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({inv} this #p m);");
        sb.AppendLine("  with r. assert (B.pts_to this #p r);");
        foreach (var f in arrays)
            sb.AppendLine($"  with {Names.Contents(f.Name)}. assert " +
                          $"(A.pts_to r.{Names.Field(f.Name)} #p {Names.Contents(f.Name)});");
        foreach (var f in objects)
            sb.AppendLine($"  with {Names.SubModel(f.Name)}. assert " +
                          $"({SubInv(f.Type)} r.{Names.Field(f.Name)} #p {Names.SubModel(f.Name)});");
        sb.AppendLine($"  unfold ({inv} this #q alt_m);");
        sb.AppendLine("  with alt_r. assert (B.pts_to this #q alt_r);");
        foreach (var f in arrays)
            sb.AppendLine($"  with {Names.Alt(Names.Contents(f.Name))}. assert " +
                          $"(A.pts_to alt_r.{Names.Field(f.Name)} #q {Names.Alt(Names.Contents(f.Name))});");
        foreach (var f in objects)
            sb.AppendLine($"  with {Names.Alt(Names.SubModel(f.Name))}. assert " +
                          $"({SubInv(f.Type)} alt_r.{Names.Field(f.Name)} #q " +
                          $"{Names.Alt(Names.SubModel(f.Name))});");
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
            sb.AppendLine($"  rewrite (A.pts_to alt_r.{Names.Field(f.Name)} #q {alt})");
            sb.AppendLine($"       as (A.pts_to r.{Names.Field(f.Name)} #q {alt});");
        }
        foreach (var f in objects)
        {
            var alt = Names.Alt(Names.SubModel(f.Name));
            sb.AppendLine($"  rewrite ({SubInv(f.Type)} alt_r.{Names.Field(f.Name)} #q {alt})");
            sb.AppendLine($"       as ({SubInv(f.Type)} r.{Names.Field(f.Name)} #q {alt});");
        }
        sb.AppendLine("  B.gather this;");
        foreach (var f in arrays)
            sb.AppendLine($"  A.gather r.{Names.Field(f.Name)};");
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
        sb.AppendLine($"ghost fn {Names.ClassInvGather(c.Name)} (this: {ty}) " +
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
    private static string Resources(
        IrClass c, ImmutableArray<IrFieldDecl> arrays, ImmutableArray<IrFieldDecl> objects,
        string perm, string record, Func<string, string> contents, Func<string, string> submodel)
    {
        var parts = new List<string> { $"B.pts_to this #{perm} {record}" };
        parts.AddRange(arrays.Select(f =>
            $"A.pts_to {record}.{Names.Field(f.Name)} #{perm} {contents(f.Name)}"));
        parts.AddRange(objects.Select(f =>
            $"{SubInv(f.Type)} {record}.{Names.Field(f.Name)} #{perm} {submodel(f.Name)}"));
        return string.Join(" ** ", parts);
    }

    // =======================================================================
    // Methods (R4.1)
    // =======================================================================

    private EmittedModule EmitMethod(IrMethod method)
    {
        var body = new CodeEmitter(_spec, diagnostics, _classes);
        var plan = new MethodPlan(method, _spec, diagnostics);

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.FunctionModule(method.Name)}");
        sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        foreach (var open in Dependencies(
                     Names.FunctionModule(method.Name), method.Body,
                     method.Requires, method.Ensures, method.Preserves))
            sb.AppendLine($"open {open}");
        sb.AppendLine(Preamble.Opens);
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();

        var origins = ImmutableArray.CreateBuilder<LineOrigin>();

        origins.Add(new LineOrigin(Lines(sb) + 1, method.Loc));
        sb.Append("fn ").Append(Names.Function(method.Name));
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

        return new EmittedModule(Names.FunctionModule(method.Name), sb.ToString())
        {
            Origins = origins.ToImmutable(),
        };
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
    private static ImmutableArray<string> Dependencies(
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
                case IrExprStmt e: CollectExpr(e.Expr); return;
                case IrGhostStmt g: CollectExpr(g.Prop); return;
                default: return;
            }
        }

        void CollectExpr(IrExpr? e)
        {
            switch (e)
            {
                case null: return;
                case IrCall c:
                    names.Add(c.Kind is CalleeKind.Spec or CalleeKind.Lemma
                        ? Names.SpecModule(c.Callee)
                        : Names.FunctionModule(c.Callee));
                    foreach (var a in c.Args) CollectExpr(a);
                    return;
                case IrBinary b: CollectExpr(b.Left); CollectExpr(b.Right); return;
                case IrUnary u: CollectExpr(u.Operand); return;
                case IrConditional t: CollectExpr(t.Cond); CollectExpr(t.Then); CollectExpr(t.Else); return;
                case IrElement el: CollectExpr(el.Array); CollectExpr(el.Index); return;
                case IrLength l: CollectExpr(l.Array); return;
                case IrOld o: CollectExpr(o.Operand); return;
                case IrNewArray na: CollectExpr(na.Length); return;
                case IrContents ct: CollectExpr(ct.Array); return;
                case IrSeqOp s: foreach (var a in s.Args) CollectExpr(a); return;
                case IrQuantifier q: CollectExpr(q.Body); return;
                case IrConvert cv: CollectExpr(cv.Operand); return;
                default: return;
            }
        }

        names.Remove(self);
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
        """;
}
