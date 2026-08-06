using System.Collections.Immutable;
using System.Text;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// doc/translation.md §9. The inheritance encoding: an abstract class becomes a vtable
/// type, an object record, and a reference type that is <c>FStar.Dyn.dyn</c>; a leaf
/// keeps its M2 representation and gains a forgetting function, a base-model view of its
/// own invariant, a vtable value and an upcast.
///
/// <para>
/// Nothing here is invented. Every construct appears in
/// <c>test/pulse_facts/ShapeHierarchy.fst</c>, which was written and verified before this
/// file existed, exactly as §0 rule 1 requires. Where a body below looks over-explicit —
/// a <c>rewrite</c> that seems to do nothing, a slot let-bound before it is applied — it
/// is because the study found that the direct version does not typecheck, and the fact is
/// recorded in §1 (F31, F33, F34).
/// </para>
/// </summary>
public sealed class HierarchyEmitter(SpecEmitter spec, DiagnosticBag diagnostics)
{
    /// <summary>R9.19. Forwarded to the spec emitter this class owns.</summary>
    public IReadOnlyDictionary<string, string> Bases
    {
        set => spec.Bases = value;
    }

    private const string Perm = "p";
    private const string Model = "m";
    private const string Obj = "o";

    /// <summary>R9.16. The erased leaf value a downcast names: the caller's knowledge.</summary>
    private const string Witness = "c";
    private const string Ret = "ret";

    /// <summary>The permission a mutating slot demands: all of it.</summary>
    private const string Full = "1.0R";

    // =======================================================================
    // The abstract class
    // =======================================================================

    /// <summary>
    /// R9.17. What a generated module publishes and what it keeps. A declaration is
    /// <em>shared</em> (its definition is part of the interface), <em>public</em> (its
    /// signature is, its proof is not), or <em>private</em> (neither).
    ///
    /// <para>The distinction is not cosmetic. R9.8's reference type is
    /// <c>FStar.Dyn.dyn</c>, and a client that could see that could write things about a
    /// C# object no C# program can express — and would then depend on a choice §9 makes
    /// for its own convenience. Hiding it makes the dyn an implementation detail in the
    /// sense F* enforces: the implementation is checked against the interface, so the
    /// encapsulation is a proof obligation and not a convention.</para>
    /// </summary>
    private sealed class Parts
    {
        public readonly StringBuilder Iface = new();
        public readonly StringBuilder Impl = new();

        /// <summary>A definition the interface carries: the model, the vtable, a spec function.</summary>
        public void Shared(string text) => Iface.Append(text).AppendLine();

        /// <summary>A definition only the implementation sees.</summary>
        public void Private(string text) => Impl.Append(text).AppendLine();

        /// <summary>A signature the interface carries, with its definition kept back.</summary>
        public void Public(string signature, string definition)
        {
            Iface.Append("val ").Append(signature).AppendLine();
            Impl.Append(definition).AppendLine();
        }

        /// <summary>
        /// A Pulse <c>fn</c> or <c>ghost fn</c>: the interface takes the signature exactly
        /// as written and stops where the body would start, which is Pulse's own way of
        /// declaring a computation in an interface.
        /// </summary>
        public void Code(string signature, string body)
        {
            Iface.Append(signature).AppendLine();
            Impl.Append(signature).AppendLine()
                .Append(body.TrimStart('\n')).AppendLine();
        }
    }

    /// <summary>
    /// R9.9/R9.18. The whole of an abstract class: the model, the observations, the
    /// vtable, the object record, the reference type, the two invariants, and a
    /// dispatching wrapper per virtual method — split (R9.17) into what a subclass and a
    /// client may see and what only this module may.
    ///
    /// <para>R9.18. One routine emits both a root and an intermediate class, and that is a
    /// claim about the encoding rather than a saving in code. Everything below the three
    /// primitives <c>is</c>, <c>ref</c> and <c>obj_at</c> — the invariants, pack and
    /// unpack, dispatch, sharing, gathering — is written once and is the same text at
    /// every depth. A class with a parent then adds, and only adds, the derived vtable
    /// that presents it as its parent, and the two casts across that one edge. So depth is
    /// not a case in this emitter: a hierarchy of any depth is the two-level rule applied
    /// once per edge.</para>
    /// </summary>
    /// <param name="parent">The base class, or null for the root of a hierarchy.</param>
    /// <param name="inherited">
    /// The virtual methods visible at <paramref name="parent"/>, in the order its vtable
    /// declares them. This class re-declares every one of them, at <em>its</em> model:
    /// a subclass fills one vtable and one only, and R9.18's derived slots are what turn
    /// that into the parent's.
    /// </param>
    public (string Iface, string Impl) EmitAbstract(
        IrClass c, IrClass? parent,
        ImmutableArray<IrMethod> inherited, ImmutableArray<IrMethod> own)
    {
        var parts = new Parts();
        Header(parts.Iface, Names.ClassModule(c.Name));
        Header(parts.Impl, Names.ClassModule(c.Name));

        // R9.9. A slot's type is fixed by the base class, so a virtual method whose
        // signature has no implementation-independent reading has no slot. Checked once,
        // here, so that a refused method is absent from the vtable and from dispatch alike.
        var slots = inherited.Concat(own.Where(v => CheckVirtual(c, v))).ToImmutableArray();
        var model = Names.ClassModel(c.Name);

        // The model and its observations are the vocabulary every specification about this
        // class is written in, so they are the one part of it that is entirely public.
        var shared = new StringBuilder();
        EmitModelType(shared, c);
        EmitObservations(shared, c);
        parts.Shared(shared.ToString().TrimEnd('\n'));

        // R9.6. An intermediate class refines its parent exactly as a leaf does, and by the
        // same declaration: the `override` of the parent's `[Model]` member.
        if (parent is not null) parts.Shared(Forget(c, parent));

        // R9.9. One field per virtual method, at *this* class's model, plus the two
        // things a vtable must carry that no C# declaration mentions: the representation
        // type, and how a permission splits over it. A subclass builds one of these, so it
        // is shared — it is the class's dispatch interface, not its encoding.
        var vtbl = new StringBuilder();
        vtbl.AppendLine($"noeq type {Names.ClassVtbl(c.Name)} = {{");
        vtbl.AppendLine("  impl : Type0;");
        vtbl.AppendLine();
        vtbl.AppendLine($"  inv : impl -> perm -> {model} -> slprop;");
        foreach (var v in slots)
        {
            vtbl.AppendLine();
            vtbl.AppendLine($"  {Names.VtblSlot(Member(v))} : ({SlotType(c, v)});");
        }
        // R9.11. R3.10d emits share and gather per class because their proofs recurse into
        // the class's own fields. Behind a dyn there is no structure to recurse into, so
        // they become dispatched operations and the leaf supplies the bodies it already
        // has. They are `stt_ghost`, which is why aliasing a `Shape` stays free at runtime.
        vtbl.AppendLine();
        vtbl.AppendLine($"  vshare : (x: impl -> #{Perm}: perm -> #{Model}: erased {model} ->");
        vtbl.AppendLine("            stt_ghost unit emp_inames");
        vtbl.AppendLine($"              (inv x {Perm} {Model})");
        vtbl.AppendLine($"              (fun _ -> inv x ({Perm} /. 2.0R) {Model} ** inv x ({Perm} /. 2.0R) {Model}));");
        vtbl.AppendLine();
        vtbl.AppendLine($"  vgather : (x: impl -> {Perm}: perm -> q: perm ->" +
                      $" #{Model}: erased {model} -> #{Names.Alt(Model)}: erased {model} ->");
        vtbl.AppendLine("             stt_ghost unit emp_inames");
        vtbl.AppendLine($"               (inv x {Perm} {Model} ** inv x q {Names.Alt(Model)})");
        vtbl.AppendLine($"               (fun _ -> inv x ({Perm} +. q) {Model} **" +
                      $" pure (reveal {Model} == reveal {Names.Alt(Model)})));");
        vtbl.Append("}");
        parts.Shared(vtbl.ToString());

        var obj = Names.ClassObj(c.Name);
        var at = Names.ClassAt(c.Name);
        var inv = Names.ClassInv(c.Name);
        var invAt = Names.ClassInvAt(c.Name);
        var self = Names.ClassType(c.Name);
        var isP = Names.ClassIs(c.Name);
        var objAt = Names.ClassObjAt(c.Name);

        // F28: a vtable together with a value of *its* implementation type is far too big
        // to live in a heap cell or an array. A subclass names one of these as the index
        // its casts are stated at, so it too is part of the interface.
        // R9.18. `sub` is the extension point, and the one field the two-level scheme did
        // not need. A class *between* this one and a leaf adds virtual methods this class
        // has never heard of, and a reference of this static type must still reach them,
        // because in this encoding the reference *is* the object. So the class declares one
        // field of the erased type `Dn.dyn` and says nothing whatever about its contents;
        // a descendant stores its own object record there, and its own invariant is what
        // says what is in it. A direct leaf stores `Dn.mkdyn ()`.
        //
        // Open-world, which is the point: the class is compiled once and admits subclasses
        // that do not exist yet. A sum over the known subclasses — the obvious cheaper
        // encoding — would not. It hangs off the *object* and not the vtable because what a
        // descendant needs back is a vtable applied to a representation; recovering a bare
        // vtable would leave its `impl` only propositionally equal to `pkg.impl`. Nothing is
        // stored twice at runtime: `sub` and the object are the same reference.
        parts.Shared($"noeq type {obj} = {{ pkg: {Names.ClassVtbl(c.Name)}; rep: pkg.impl;" +
                     " sub: Dn.dyn }");

        // R9.18. The derived vtable: this class presented as its parent. It is what makes
        // the parent's `impl` this class's *reference* type rather than a leaf's
        // representation, and so what lets a leaf implement one vtable and get every
        // ancestor's for free.
        if (parent is not null) EmitDerived(parts, c, parent, inherited);

        // R9.8/R9.17. F29 promotes the pair into `dyn`, which is `Type0` and therefore
        // boxable, array-able, and admissible as a field — and *that* is the choice a
        // client must not see, because nothing in C# corresponds to it.
        // R9.18. An intermediate class's references *are* its parent's: an upcast changes
        // the invariant and never the value, so there is one reference type per hierarchy
        // and the dyn is made once, at the root.
        parts.Public($"{self} : Type0",
            $"let {self} : Type0 = " +
            (parent is null ? "Dn.dyn" : $"{Names.ClassModule(parent.Name)}.{Names.ClassType(parent.Name)}"));

        // F34: named apart from the invariant so that a `fold` can be handed an explicit
        // witness for the existential. Private: it mentions nothing but is the shape of
        // the encoding, and everything a subclass needs from it is `pack` and `unpack`.
        parts.Private($"let {at} (o: {obj}) ({Perm}: perm) ({Model}: {model}) : slprop =" +
                      $" o.pkg.inv o.rep {Perm} {Model}");

        // R9.18. "This reference denotes this object record". At the root that is what
        // `mkdyn` says; at an intermediate class it is the parent's own `is` about the
        // record this one presents as. Abstract, because it is the encoding: what a client
        // and a subclass need from it is that it is *some* proposition the three primitives
        // below agree on.
        parts.Public($"{isP} (s: {self}) (o: {obj}) : prop",
            $"let {isP} (s: {self}) (o: {obj}) : prop = " +
            (parent is null
                ? $"(s == Dn.mkdyn o)"
                : $"{Names.ClassModule(parent.Name)}.{Names.ClassIs(parent.Name)} s ({Names.ClassView(c.Name)} o)"));

        // R9.9. The same signature an M2 class invariant has (§3.4), which is why a client
        // of a hierarchy needs no new rules: R4.5's model binders, R4.10's fold/unfold
        // bracket, R3.10b's nested objects and R5.12's loops all apply unchanged. The
        // *signature* is all of that; the body is where the dyn is.
        var invSig = $"{inv} (s: {self}) (#[T.exact (`{Full})] {Perm}: perm)" +
                     $" ({Model}: {model}) : slprop";
        parts.Public(invSig,
            $"let {invSig} =\n" +
            $"  exists* ({Obj}: {obj}). pure ({isP} s {Obj}) ** {at} {Obj} {Perm} {Model}");

        // R9.10. The primitive form, with the object record named. `gather` forces it —
        // two views of one object otherwise unfold to separate witnesses related only by
        // `s == mkdyn o1` and `s == mkdyn o2`, and equating those is injectivity of
        // `mkdyn`, which is Cantor-inconsistent. A checked downcast needs the same index.
        var invAtSig = $"{invAt} (s: {self}) ({Obj}: erased {obj}) ({Perm}: perm)" +
                       $" ({Model}: {model}) : slprop";
        parts.Public(invAtSig,
            $"let {invAtSig} =\n" +
            $"  pure ({isP} s (reveal {Obj})) ** {at} {Obj} {Perm} {Model}");

        // R9.10. Forgetting is one ghost step, and irreversible: recovering the index from
        // the plain invariant would again be injectivity of `mkdyn`.
        parts.Code(
            $"ghost fn {Names.ClassForgetImpl(c.Name)} (s: {self}) ({Obj}: erased {obj})" +
            $" (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {invAt} s {Obj} {Perm} {Model}\n" +
            $"  ensures  {inv} s #{Perm} {Model}",
            "{\n" +
            $"  unfold ({invAt} s {Obj} {Perm} {Model});\n" +
            $"  fold ({inv} s #{Perm} {Model});\n" +
            "}");

        // R9.18. Opening and closing the indexed invariant. A descendant has to reach the
        // resource its parent's invariant carries, in order to re-read it at its own model;
        // since the definition is not exported these two are the only way, and they are
        // what the casts across one inheritance edge are written with.
        var raw = $"(reveal {Obj}).pkg.inv (reveal {Obj}).rep {Perm} {Model}";
        parts.Code(
            $"ghost fn {Names.ClassElimAt(c.Name)} (s: {self}) ({Obj}: erased {obj})" +
            $" (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {invAt} s {Obj} {Perm} {Model}\n" +
            $"  ensures  {raw} ** pure ({isP} s (reveal {Obj}))",
            "{\n" +
            $"  unfold ({invAt} s {Obj} {Perm} {Model});\n" +
            $"  rewrite ({at} {Obj} {Perm} {Model}) as ({raw});\n" +
            "}");

        parts.Code(
            $"ghost fn {Names.ClassIntroAt(c.Name)} (s: {self}) ({Obj}: erased {obj})" +
            $" (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {raw} ** pure ({isP} s (reveal {Obj}))\n" +
            $"  ensures  {invAt} s {Obj} {Perm} {Model}",
            "{\n" +
            $"  rewrite ({raw}) as ({at} {Obj} {Perm} {Model});\n" +
            $"  fold ({invAt} s {Obj} {Perm} {Model});\n" +
            "}");

        // R9.18. Making a reference from an object record, and recovering the record from
        // the reference. These two and `is` are the whole of what an encoding supplies; at
        // the root they are `mkdyn` and R9.13's recovery, and at an intermediate class they
        // are the parent's, one `sub` field further in.
        parts.Code(
            $"fn {Names.ClassRef(c.Name)} (o: {obj})\n" +
            $"  returns  s: {self}\n" +
            $"  ensures  pure ({isP} s o)",
            "{\n" +
            (parent is null
                ? "  (Dn.mkdyn o)\n"
                : $"  ({Names.ClassModule(parent.Name)}.{Names.ClassRef(parent.Name)}" +
                  $" ({Names.ClassView(c.Name)} o))\n") +
            "}");

        parts.Code(
            $"fn {objAt} (s: {self}) ({Obj}: erased {obj})\n" +
            $"  requires pure ({isP} s (reveal {Obj}))\n" +
            $"  returns  ob: {obj}\n" +
            $"  ensures  pure (ob == reveal {Obj})",
            "{\n" +
            (parent is null
                ? $"  CAs.recover #{obj} #{Obj} s\n"
                // R9.18. One level further: the parent hands back the record this class
                // presents as, and `sub` is where that record put this one.
                : $"  let pob = {Names.ClassModule(parent.Name)}.{Names.ClassObjAt(parent.Name)}" +
                  $" s (hide ({Names.ClassView(c.Name)} (reveal {Obj})));\n" +
                  $"  CAs.recover #{obj} #{Obj} pob.sub\n") +
            "}");

        // R9.17. The two operations that make the dyn private. `pack` is what a reference
        // conversion is (R9.15): an object record becomes a reference, and the invariant
        // follows it. Every subclass's upcast is this call, so `Dn.mkdyn` is written once
        // in the whole translation.
        parts.Code(
            $"fn {Names.ClassPack(c.Name)} ({Obj}: {obj}) (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {Obj}.pkg.inv {Obj}.rep {Perm} {Model}\n" +
            $"  returns  s: {self}\n" +
            $"  ensures  {invAt} s (hide {Obj}) {Perm} {Model}",
            "{\n" +
            $"  let s = {Names.ClassRef(c.Name)} {Obj};\n" +
            $"  rewrite ({Obj}.pkg.inv {Obj}.rep {Perm} {Model}) as ({at} {Obj} {Perm} {Model});\n" +
            $"  fold ({invAt} s (hide {Obj}) {Perm} {Model});\n" +
            "  s\n" +
            "}");

        // R9.16/R9.17. And `unpack` is what a checked downcast is: a reference whose index
        // names the record it was packed from gives that record's representation back.
        // Reading `o.rep` out directly would need a coercion across `o.pkg.impl == impl`,
        // which is only propositionally true; going back through `mkdyn` keeps everything
        // a dyn, and congruence on the box then delivers the equation `recover` asks for.
        var pkg = "v";
        var made = $"({{ pkg = {pkg}; rep = reveal x; sub = reveal sub }})";
        parts.Private($"let {Names.ClassBox(c.Name)} (o: {obj}) : Dn.dyn = Dn.mkdyn o.rep");

        parts.Code(
            $"fn {Names.ClassUnpack(c.Name)} ({pkg}: {Names.ClassVtbl(c.Name)}) (x: erased {pkg}.impl)" +
            $" (sub: erased Dn.dyn) (s: {self}) (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {invAt} s (hide {made}) {Perm} {Model}\n" +
            $"  returns  r: {pkg}.impl\n" +
            $"  ensures  {pkg}.inv r {Perm} {Model} ** pure (r == reveal x)",
            "{\n" +
            $"  unfold ({invAt} s (hide {made}) {Perm} {Model});\n" +
            $"  let ob = {objAt} s (hide {made});\n" +
            $"  let r = CAs.recover #{pkg}.impl #x ({Names.ClassBox(c.Name)} ob);\n" +
            $"  rewrite ({at} {made} {Perm} {Model}) as ({pkg}.inv r {Perm} {Model});\n" +
            "  r\n" +
            "}");

        EmitShareGather(parts, c);
        foreach (var v in slots) EmitDispatch(parts, c, v);

        // R9.18. The two casts across this one inheritance edge. They are the *whole* of
        // what depth costs: a client that upcasts a Square to a Shape does it in two steps,
        // each of which is the two-level rule, and neither step knows about the other.
        if (parent is not null) EmitInnerCasts(parts, c, parent);

        return (parts.Iface.ToString(), parts.Impl.ToString());
    }

    /// <summary>
    /// R9.6. The base's model as a function of this class's — the <c>override</c> of the
    /// base's <c>[Model]</c> member. Identical for an intermediate class and a leaf, which
    /// is the point: a class is a refinement of its parent for the same reason at every
    /// depth.
    /// </summary>
    private string Forget(IrClass c, IrClass parent)
    {
        var pModel = $"{Names.ClassModule(parent.Name)}.{Names.ClassModel(parent.Name)}";
        var scope = new SpecScope { DefiningClass = c.Name };
        scope.Bind(c.ModelMember, new Term(Model, MethodPlan.KindOf(c.ModelType), c.ModelType));
        var forget = c.ForgetBody is null
            ? Model
            : MethodPlan.KindOf(parent.ModelType) == TermKind.Math
                ? spec.Math(c.ForgetBody, scope)
                : spec.Emit(c.ForgetBody, scope).Text;
        return $"let {Names.ClassForget(c.Name)} ({Model}: {Names.ClassModel(c.Name)}) : {pModel} =\n" +
               $"  {forget}";
    }

    /// <summary>
    /// R9.18. The derived vtable: an arbitrary vtable of this class, read as one of its
    /// parent's.
    ///
    /// <para>This is the whole content of "an intermediate class is still a subclass". The
    /// parent's <c>impl</c> is instantiated to *this* class's representation type, its
    /// <c>inv</c> to this class's invariant existentially quantified over the models that
    /// forget to the parent's, and each of its slots to a wrapper that opens that
    /// existential, dispatches one level down and closes it again. A leaf therefore fills
    /// exactly one vtable — its immediate parent's — and every ancestor's follows.</para>
    /// </summary>
    private void EmitDerived(Parts parts, IrClass c, IrClass parent, ImmutableArray<IrMethod> inherited)
    {
        var pMod = Names.ClassModule(parent.Name);
        var pModel = $"{pMod}.{Names.ClassModel(parent.Name)}";
        var vtbl = Names.ClassVtbl(c.Name);
        var asBase = Names.ClassAsBase(c.Name, parent.Name);
        var forget = Names.ClassForget(c.Name);
        var own = "own";

        // R9.14, at a vtable rather than at a reference: the same view a leaf takes of its
        // own invariant, taken instead of a vtable applied to a representation, because
        // that is what an intermediate class has and a leaf's representation is not.
        parts.Private(
            $"let {asBase} (qp: {vtbl}) (x: qp.impl) ({Perm}: perm) ({Model}: {pModel}) : slprop =\n" +
            $"  exists* ({own}: {Names.ClassModel(c.Name)}). qp.inv x {Perm} {own} **" +
            $" pure ({Model} == {forget} {own})");

        foreach (var v in inherited) EmitDerivedSlot(parts, c, parent, v);

        var half = $"({Perm} /. 2.0R)";
        var alt = Names.Alt(Model);
        parts.Private(
            $"ghost fn {Names.ClassPkgSlot(c.Name, "share")} (qp: {vtbl}) (x: qp.impl)" +
            $" (#{Perm}: perm) (#{Model}: erased {pModel})\n" +
            $"  requires {asBase} qp x {Perm} {Model}\n" +
            $"  ensures  {asBase} qp x {half} {Model} ** {asBase} qp x {half} {Model}\n" +
            "{\n" +
            $"  unfold ({asBase} qp x {Perm} {Model});\n" +
            $"  with {own}. assert (qp.inv x {Perm} {own});\n" +
            "  let f = qp.vshare;\n" +
            $"  f x #{Perm} #{own};\n" +
            $"  fold ({asBase} qp x {half} {Model});\n" +
            $"  fold ({asBase} qp x {half} {Model});\n" +
            "}");

        parts.Private(
            "[@@allow_ambiguous]\n" +
            $"ghost fn {Names.ClassPkgSlot(c.Name, "gather")} (qp: {vtbl}) (x: qp.impl)" +
            $" ({Perm}: perm) (q: perm) (#{Model}: erased {pModel}) (#{alt}: erased {pModel})\n" +
            $"  requires {asBase} qp x {Perm} {Model} ** {asBase} qp x q {alt}\n" +
            $"  ensures  {asBase} qp x ({Perm} +. q) {Model} **" +
            $" pure (reveal {Model} == reveal {alt})\n" +
            "{\n" +
            $"  unfold ({asBase} qp x {Perm} {Model});\n" +
            $"  with {own}. assert (qp.inv x {Perm} {own});\n" +
            $"  unfold ({asBase} qp x q {alt});\n" +
            $"  with {own}2. assert (qp.inv x q {own}2);\n" +
            "  let g = qp.vgather;\n" +
            $"  g x {Perm} q #{own} #{own}2;\n" +
            $"  fold ({asBase} qp x ({Perm} +. q) {Model});\n" +
            "}");

        // F33 again: the meta-argument-defaulted permission binder does not match a vtable
        // field type, so every slot is eta-expanded here exactly as a leaf's is.
        var pkg = new StringBuilder();
        pkg.AppendLine($"let {Names.ClassBasePkg(c.Name, parent.Name)} (qp: {vtbl}) :" +
                       $" {pMod}.{Names.ClassVtbl(parent.Name)} = {{");
        pkg.AppendLine("  impl = qp.impl;");
        pkg.AppendLine($"  inv = (fun (x: qp.impl) ({Perm}: perm) ({Model}: {pModel}) ->" +
                       $" {asBase} qp x {Perm} {Model});");
        foreach (var v in inherited)
        {
            var moves = !v.IsReadOnly;
            var args = string.Concat(Value(v).Select(p => $" ({Names.Local(p.Name)}: {Types.Render(p.Type)})"));
            var pass = string.Concat(Value(v).Select(p => " " + Names.Local(p.Name)));
            var permB = moves ? "" : $" (#{Perm}: perm)";
            var permA = moves ? "" : $" #{Perm}";
            pkg.AppendLine($"  {Names.VtblSlot(Member(v))} = (fun (x: qp.impl){args}{permB}" +
                           $" (#{Model}: erased {pModel}) ->");
            pkg.AppendLine($"    {Names.ClassPkgSlot(c.Name, Member(v))} qp x{pass}{permA} #{Model});");
        }
        pkg.AppendLine($"  vshare = (fun (x: qp.impl) (#{Perm}: perm) (#{Model}: erased {pModel}) ->");
        pkg.AppendLine($"    {Names.ClassPkgSlot(c.Name, "share")} qp x #{Perm} #{Model});");
        pkg.AppendLine($"  vgather = (fun (x: qp.impl) ({Perm}: perm) (q: perm)" +
                       $" (#{Model}: erased {pModel}) (#{alt}: erased {pModel}) ->");
        pkg.AppendLine($"    {Names.ClassPkgSlot(c.Name, "gather")} qp x {Perm} q #{Model} #{alt});");
        pkg.Append("}");
        parts.Private(pkg.ToString());

        // R9.18. The parent object record a value of this class presents as. `sub` carries
        // this class's own record back, so the view is a pure function and both casts are
        // free: the reference is the same value, and only the invariant changes.
        parts.Public(
            $"{Names.ClassView(c.Name)} (o: {Names.ClassObj(c.Name)}) : {pMod}.{Names.ClassObj(parent.Name)}",
            $"let {Names.ClassView(c.Name)} (o: {Names.ClassObj(c.Name)}) :" +
            $" {pMod}.{Names.ClassObj(parent.Name)} =\n" +
            $"  {{ pkg = {Names.ClassBasePkg(c.Name, parent.Name)} o.pkg; rep = o.rep;" +
            " sub = Dn.mkdyn o }");
    }

    /// <summary>
    /// R9.18. One inherited method's derived implementation: open the existential the
    /// parent's view hides, dispatch through <em>this</em> class's vtable, close it again.
    ///
    /// <para>The proof that the parent's contract holds is the whole of R9.7 restated one
    /// level up, and is discharged by the model equation alone: the slot's own contract is
    /// this class's reading of the same C# annotation, which R9.19 composes with
    /// <c>forget</c>, and the view says the parent's model *is* that composition.</para>
    /// </summary>
    private void EmitDerivedSlot(Parts parts, IrClass c, IrClass parent, IrMethod v)
    {
        var pMod = Names.ClassModule(parent.Name);
        var pModel = $"{pMod}.{Names.ClassModel(parent.Name)}";
        var asBase = Names.ClassAsBase(c.Name, parent.Name);
        var (pre, post) = Contract(parent, v, Model, out var moves, c);
        var perm = moves ? Full : Perm;
        var own = "own";
        var postOwn = "post_own";
        var args = string.Concat(Value(v).Select(p => " " + Names.Local(p.Name)));
        var binders = string.Concat(Value(v).Select(p => $" ({Names.Local(p.Name)}: {Types.Render(p.Type)})"));
        var permBinder = moves ? "" : $" (#{Perm}: perm)";
        var isVoid = v.ReturnType is IrPrim { Kind: PrimKind.Void };

        var sig = new StringBuilder();
        sig.AppendLine($"fn {Names.ClassPkgSlot(c.Name, Member(v))} (qp: {Names.ClassVtbl(c.Name)})" +
                       $" (x: qp.impl){binders}{permBinder} (#{Model}: erased {pModel})");
        sig.AppendLine($"  requires {asBase} qp x {perm} {Model}{Pure(pre)}");
        if (!isVoid) sig.AppendLine($"  returns  {Ret}: {Types.Render(v.ReturnType)}");
        sig.Append(moves
            ? $"  ensures  exists* {PostModel}. {asBase} qp x {perm} {PostModel}{Pure(post)}"
            : $"  ensures  {asBase} qp x {perm} {Model}{Pure(post)}");

        var body = new StringBuilder();
        body.AppendLine("{");
        body.AppendLine($"  unfold ({asBase} qp x {perm} {Model});");
        body.AppendLine($"  with {own}. assert (qp.inv x {perm} {own});");
        // F31: a stored Pulse computation must be let-bound before it is applied.
        body.AppendLine($"  let f = qp.{Names.VtblSlot(Member(v))};");
        var call = $"f x{args}{(moves ? "" : $" #{Perm}")} #{own};";
        if (moves)
        {
            body.AppendLine($"  {call}");
            body.AppendLine($"  with {postOwn}. assert (qp.inv x {perm} {postOwn});");
            body.AppendLine($"  fold ({asBase} qp x {perm} ({Names.ClassForget(c.Name)} {postOwn}));");
        }
        else
        {
            body.AppendLine(isVoid ? $"  {call}" : $"  let {Ret}0 = {call}");
            body.AppendLine($"  fold ({asBase} qp x {perm} {Model});");
            if (!isVoid) body.AppendLine($"  {Ret}0");
        }
        body.Append("}");
        parts.Private(sig + "\n" + body);
    }

    /// <summary>
    /// R9.18. The two casts across one inheritance edge, for an intermediate class. They
    /// are R9.15a and R9.16 with the leaf's representation replaced by this class's object
    /// record, and they are ghost in substance: the reference handed back is the one that
    /// came in, because in this encoding an upcast changes the invariant and not the value.
    /// </summary>
    private static void EmitInnerCasts(Parts parts, IrClass c, IrClass parent)
    {
        var pMod = Names.ClassModule(parent.Name);
        var pModel = $"{pMod}.{Names.ClassModel(parent.Name)}";
        var model = Names.ClassModel(c.Name);
        var obj = Names.ClassObj(c.Name);
        var self = Names.ClassType(c.Name);
        var asBase = Names.ClassAsBase(c.Name, parent.Name);
        var view = $"({Names.ClassView(c.Name)} (reveal {Obj}))";
        var pInvAt = $"{pMod}.{Names.ClassInvAt(parent.Name)}";
        var forget = $"({Names.ClassForget(c.Name)} {Model})";
        var raw = $"{view}.pkg.inv {view}.rep {Perm}";

        parts.Code(
            $"fn {Names.UpcastToAt(c.Name, parent.Name)} (s: {self}) ({Obj}: erased {obj})" +
            $" (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {Names.ClassInvAt(c.Name)} s {Obj} {Perm} {Model}\n" +
            $"  returns  r: {pMod}.{Names.ClassType(parent.Name)}\n" +
            $"  ensures  {pInvAt} r (hide {view}) {Perm} {forget}",
            "{\n" +
            $"  {Names.ClassElimAt(c.Name)} s {Obj} #{Perm} #{Model};\n" +
            $"  fold ({asBase} (reveal {Obj}).pkg (reveal {Obj}).rep {Perm} {forget});\n" +
            $"  rewrite ({asBase} (reveal {Obj}).pkg (reveal {Obj}).rep {Perm} {forget})" +
            $" as ({raw} {forget});\n" +
            $"  {pMod}.{Names.ClassIntroAt(parent.Name)} s (hide {view}) #{Perm} #{forget};\n" +
            "  s\n" +
            "}");

        // R9.18. And with the index dropped. A `Quadrilateral` this method was handed
        // rather than made has no known object record, and C# converts it to a `Shape`
        // just the same; the index is what a later downcast needs, so a conversion that
        // starts without one ends without one.
        parts.Code(
            $"fn {Names.UpcastTo(c.Name, parent.Name)} (s: {self})" +
            $" (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {Names.ClassInv(c.Name)} s #{Perm} {Model}\n" +
            $"  returns  r: {pMod}.{Names.ClassType(parent.Name)}\n" +
            $"  ensures  {pMod}.{Names.ClassInv(parent.Name)} r #{Perm} {forget}",
            "{\n" +
            $"  unfold ({Names.ClassInv(c.Name)} s #{Perm} {Model});\n" +
            $"  with {Obj}. assert ({Names.ClassAt(c.Name)} {Obj} {Perm} {Model});\n" +
            $"  fold ({Names.ClassInvAt(c.Name)} s (hide {Obj}) {Perm} {Model});\n" +
            $"  let r = {Names.UpcastToAt(c.Name, parent.Name)} s (hide {Obj}) #{Perm} #{Model};\n" +
            $"  {pMod}.{Names.ClassForgetImpl(parent.Name)} r" +
            $" (hide ({Names.ClassView(c.Name)} {Obj})) #{Perm} #{forget};\n" +
            "  r\n" +
            "}");

        // R9.16. The checked downcast across the inner edge. What the caller must know is
        // *which* object record the reference denotes, and that is exactly what C# would
        // test for; the model it gets back is existential because forgetting is not
        // injective — a Shape model does not determine the Quadrilateral it came from.
        parts.Code(
            $"fn {Names.DowncastFrom(c.Name, parent.Name)} (s: {pMod}.{Names.ClassType(parent.Name)})" +
            $" (#{Obj}: erased {obj}) (#{Perm}: perm) (#{Model}: erased {pModel})\n" +
            $"  requires {pInvAt} s (hide {view}) {Perm} {Model}\n" +
            $"  returns  r: {self}\n" +
            $"  ensures  exists* own. {Names.ClassInvAt(c.Name)} r {Obj} {Perm} own **" +
            $" pure (reveal {Model} == {Names.ClassForget(c.Name)} own)",
            "{\n" +
            $"  {pMod}.{Names.ClassElimAt(parent.Name)} s (hide {view}) #{Perm} #{Model};\n" +
            $"  rewrite ({raw} {Model})" +
            $" as ({asBase} (reveal {Obj}).pkg (reveal {Obj}).rep {Perm} {Model});\n" +
            $"  unfold ({asBase} (reveal {Obj}).pkg (reveal {Obj}).rep {Perm} {Model});\n" +
            $"  with own. assert ((reveal {Obj}).pkg.inv (reveal {Obj}).rep {Perm} own);\n" +
            $"  {Names.ClassIntroAt(c.Name)} s {Obj} #{Perm} #own;\n" +
            "  s\n" +
            "}");
    }

    /// <summary>
    /// R9.9. A vtable slot's type: the virtual method's contract with the receiver read as
    /// the vtable's own <c>inv x p m</c>. It is generated here rather than through
    /// <see cref="MethodPlan"/> because a slot's <c>inv</c> takes its permission
    /// positionally, where R4.10's takes it as F21's meta-argument-defaulted implicit.
    /// </summary>
    private string SlotType(IrClass c, IrMethod v)
    {
        var model = Names.ClassModel(c.Name);
        var (pre, post) = Contract(c, v, Model, out var moves);

        var binders = new StringBuilder("x: impl");
        foreach (var p in Value(v)) binders.Append($" -> {Names.Local(p.Name)}: {Types.Render(p.Type)}");
        // R4.11b/F26: a read-only slot is generalised over the permission, so a shape held
        // at any fraction may be measured; a mutating one demands all of it.
        if (!moves) binders.Append($" -> #{Perm}: perm");
        binders.Append($" -> #{Model}: erased {model}");

        var perm = moves ? Full : Perm;
        var result = Types.Render(v.ReturnType);
        var body = new StringBuilder();
        body.Append($"{binders} ->\n           stt {result} (inv x {perm} {Model}{Pure(pre)})\n");
        body.Append(moves
            ? $"                      (fun {Ret} -> exists* {PostModel}. inv x {perm} {PostModel}{Pure(post)})"
            : $"                      (fun {Ret} -> inv x {perm} {Model}{Pure(post)})");
        return body.ToString();
    }

    /// <summary>R9.12. The dispatching wrapper, at the index and then plain (R9.10).</summary>
    private void EmitDispatch(Parts parts, IrClass c, IrMethod v)
    {
        var model = Names.ClassModel(c.Name);
        var self = Names.ClassType(c.Name);
        var obj = Names.ClassObj(c.Name);
        var at = Names.ClassAt(c.Name);
        var invAt = Names.ClassInvAt(c.Name);
        var inv = Names.ClassInv(c.Name);
        var (pre, post) = Contract(c, v, Model, out var moves);
        var perm = moves ? Full : Perm;
        var args = string.Concat(Value(v).Select(p => " " + Names.Local(p.Name)));
        var binders = string.Concat(Value(v).Select(p => $" ({Names.Local(p.Name)}: {Types.Render(p.Type)})"));
        var permBinder = moves ? "" : $" (#{Perm}: perm)";
        var returns = v.ReturnType is IrPrim { Kind: PrimKind.Void }
            ? "" : $"  returns {Ret}: {Types.Render(v.ReturnType)}\n";

        // The indexed form is the one that dispatches (R9.10).
        var sb = new StringBuilder();
        sb.AppendLine($"fn {Names.DispatchAt(c.Name, Member(v))} (s: {self}){binders}" +
                      $" (#{Obj}: erased {obj}){permBinder} (#{Model}: erased {model})");
        sb.AppendLine($"  requires {invAt} s {Obj} {perm} {Model}{Pure(pre)}");
        sb.Append(returns);
        sb.Append(moves
            ? $"  ensures  exists* {PostModel}. {invAt} s {Obj} {perm} {PostModel}{Pure(post)}"
            : $"  ensures  {invAt} s {Obj} {perm} {Model}{Pure(post)}");

        var body = new StringBuilder();
        body.AppendLine("{");
        body.AppendLine($"  unfold ({invAt} s {Obj} {perm} {Model});");
        // R9.18. The record the reference denotes. At the root R9.13's recovery is the one
        // assumption behind it; at an intermediate class it is one `sub` field further in.
        // Dispatch does not know which, and that is why depth costs it nothing.
        body.AppendLine($"  let ob = {Names.ClassObjAt(c.Name)} s {Obj};");
        body.AppendLine($"  rewrite ({at} {Obj} {perm} {Model}) as ({at} ob {perm} {Model});");
        body.AppendLine($"  unfold ({at} ob {perm} {Model});");
        // F31: a stored Pulse computation must be let-bound before it is applied.
        body.AppendLine($"  let f = ob.pkg.{Names.VtblSlot(Member(v))};");
        var call = $"f ob.rep{args}{(moves ? "" : $" #{Perm}")} #{Model};";
        if (moves)
        {
            body.AppendLine($"  {call}");
            body.AppendLine($"  with {PostModel}. assert (ob.pkg.inv ob.rep {perm} {PostModel});");
            body.AppendLine($"  fold ({at} ob {perm} {PostModel});");
            body.AppendLine($"  rewrite ({at} ob {perm} {PostModel}) as ({at} {Obj} {perm} {PostModel});");
            body.AppendLine($"  fold ({invAt} s {Obj} {perm} {PostModel});");
        }
        else
        {
            body.AppendLine($"  let v = {call}");
            body.AppendLine($"  fold ({at} ob {perm} {Model});");
            body.AppendLine($"  rewrite ({at} ob {perm} {Model}) as ({at} {Obj} {perm} {Model});");
            body.AppendLine($"  fold ({invAt} s {Obj} {perm} {Model});");
            if (v.ReturnType is not IrPrim { Kind: PrimKind.Void }) body.AppendLine("  v");
        }
        body.Append("}");
        parts.Code(sb.ToString(), "\n" + body);

        // R9.10. The plain form is the indexed one composed with forgetting, so there is
        // one dispatching body per method and not two.
        var sb2 = new StringBuilder();
        sb2.AppendLine($"fn {Names.Dispatch(c.Name, Member(v))} (s: {self}){binders}" +
                       $"{permBinder} (#{Model}: erased {model})");
        sb2.AppendLine($"  requires {inv} s #{perm} {Model}{Pure(pre)}");
        sb2.Append(returns);
        sb2.Append(moves
            ? $"  ensures  exists* {PostModel}. {inv} s #{perm} {PostModel}{Pure(post)}"
            : $"  ensures  {inv} s #{perm} {Model}{Pure(post)}");

        var body2 = new StringBuilder();
        body2.AppendLine("{");
        body2.AppendLine($"  unfold ({inv} s #{perm} {Model});");
        body2.AppendLine($"  with {Obj}. assert ({at} {Obj} {perm} {Model});");
        body2.AppendLine($"  fold ({invAt} s (hide {Obj}) {perm} {Model});");
        var inner = $"{Names.DispatchAt(c.Name, Member(v))} s{args} #(hide {Obj})" +
                    $"{(moves ? "" : $" #{Perm}")} #{Model};";
        if (moves)
        {
            body2.AppendLine($"  {inner}");
            body2.AppendLine($"  with {PostModel}. assert ({invAt} s (hide {Obj}) {perm} {PostModel});");
            body2.AppendLine($"  {Names.ClassForgetImpl(c.Name)} s (hide {Obj}) #{perm} #{PostModel};");
        }
        else
        {
            body2.AppendLine($"  let v = {inner}");
            body2.AppendLine($"  {Names.ClassForgetImpl(c.Name)} s (hide {Obj}) #{perm} #{Model};");
            if (v.ReturnType is not IrPrim { Kind: PrimKind.Void }) body2.AppendLine("  v");
        }
        body2.Append("}");
        parts.Code(sb2.ToString(), "\n" + body2);
    }

    /// <summary>R9.11. Dispatched sharing and gathering, both ghost.</summary>
    private static void EmitShareGather(Parts parts, IrClass c)
    {
        var model = Names.ClassModel(c.Name);
        var self = Names.ClassType(c.Name);
        var obj = Names.ClassObj(c.Name);
        var at = Names.ClassAt(c.Name);
        var inv = Names.ClassInv(c.Name);
        var invAt = Names.ClassInvAt(c.Name);
        var alt = Names.Alt(Model);
        var half = $"({Perm} /. 2.0R)";

        parts.Code(
            $"ghost fn {Names.ClassInvShare(c.Name)}_at (s: {self}) ({Obj}: erased {obj})" +
            $" (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {invAt} s {Obj} {Perm} {Model}\n" +
            $"  ensures  {invAt} s {Obj} {half} {Model} ** {invAt} s {Obj} {half} {Model}",
            "\n{\n" +
            $"  unfold ({invAt} s {Obj} {Perm} {Model});\n" +
            $"  unfold ({at} {Obj} {Perm} {Model});\n" +
            $"  let f = {Obj}.pkg.vshare;\n" +
            $"  f {Obj}.rep #{Perm} #{Model};\n" +
            $"  fold ({at} {Obj} {half} {Model});\n" +
            $"  fold ({at} {Obj} {half} {Model});\n" +
            $"  fold ({invAt} s {Obj} {half} {Model});\n" +
            $"  fold ({invAt} s {Obj} {half} {Model});\n" +
            "}");

        parts.Code(
            $"ghost fn {Names.ClassInvShare(c.Name)} (s: {self})" +
            $" (#{Perm}: perm) (#{Model}: erased {model})\n" +
            $"  requires {inv} s #{Perm} {Model}\n" +
            $"  ensures  {inv} s #{half} {Model} ** {inv} s #{half} {Model}",
            "\n{\n" +
            $"  unfold ({inv} s #{Perm} {Model});\n" +
            $"  with {Obj}. assert ({at} {Obj} {Perm} {Model});\n" +
            $"  fold ({invAt} s (hide {Obj}) {Perm} {Model});\n" +
            $"  {Names.ClassInvShare(c.Name)}_at s (hide {Obj}) #{Perm} #{Model};\n" +
            $"  {Names.ClassForgetImpl(c.Name)} s (hide {Obj}) #{half} #{Model};\n" +
            $"  {Names.ClassForgetImpl(c.Name)} s (hide {Obj}) #{half} #{Model};\n" +
            "}");

        // Only the *indexed* gather exists. The unindexed one is unprovable: two views of
        // one object unfold to separate witnesses related only through `mkdyn`, and
        // equating them is the injectivity `ShapeHierarchy.fst` §3 pins as unavailable.
        parts.Code(
            "[@@allow_ambiguous]\n" +
            $"ghost fn {Names.ClassInvGather(c.Name)}_at (s: {self}) ({Obj}: erased {obj})" +
            $" ({Perm}: perm) (q: perm) (#{Model}: erased {model}) (#{alt}: erased {model})\n" +
            $"  requires {invAt} s {Obj} {Perm} {Model} ** {invAt} s {Obj} q {alt}\n" +
            $"  ensures  {invAt} s {Obj} ({Perm} +. q) {Model} **" +
            $" pure (reveal {Model} == reveal {alt})",
            "\n{\n" +
            $"  unfold ({invAt} s {Obj} {Perm} {Model});\n" +
            $"  unfold ({invAt} s {Obj} q {alt});\n" +
            $"  unfold ({at} {Obj} {Perm} {Model});\n" +
            $"  unfold ({at} {Obj} q {alt});\n" +
            $"  let g = {Obj}.pkg.vgather;\n" +
            $"  g {Obj}.rep {Perm} q #{Model} #{alt};\n" +
            $"  fold ({at} {Obj} ({Perm} +. q) {Model});\n" +
            $"  fold ({invAt} s {Obj} ({Perm} +. q) {Model});\n" +
            "}");
    }

    // =======================================================================
    // The leaf
    // =======================================================================

    /// <summary>
    /// R9.14. What a leaf adds to its M2 module: the forgetting function and its own
    /// invariant seen at the base's model. The vtable value comes later, in
    /// <see cref="EmitVtbl"/>, because it mentions the method modules.
    /// </summary>
    public string EmitLeafView(IrClass c, IrClass parent)
    {
        var sb = new StringBuilder();
        var pModule = Names.ClassModule(parent.Name);
        var pModel = $"{pModule}.{Names.ClassModel(parent.Name)}";
        var own = Names.ClassModel(c.Name);

        // R9.6, shared verbatim with an intermediate class: a leaf is a refinement of its
        // parent for exactly the same reason, and by exactly the same declaration.
        sb.AppendLine();
        sb.AppendLine(Forget(c, parent));
        sb.AppendLine();

        // R9.14. The leaf's own invariant read at the base's model: this is what a vtable
        // slot's `inv` is instantiated to, and it is why an `override`'s body is checked
        // against the base's contract while still seeing its own fields.
        sb.AppendLine($"let {Names.ClassAsBase(c.Name, parent.Name)} (this: {Names.ClassType(c.Name)})" +
                      $" (#[T.exact (`{Full})] {Perm}: perm) ({Model}: {pModel}) : slprop =");
        sb.AppendLine($"  exists* (own: {own}). {Names.ClassInv(c.Name)} this #{Perm} own **" +
                      $" pure ({Model} == {Names.ClassForget(c.Name)} own)");
        return sb.ToString();
    }

    /// <summary>
    /// R9.14. The vtable <em>value</em>, the object record, and the two casts. It is a
    /// module of its own because it mentions every method module, and the constructor's
    /// module mentions it.
    ///
    /// <para>R9.17: what a client of the cast needs is the two casts and the index they
    /// are stated at; the vtable value that makes them work is this module's own business,
    /// and neither <c>FStar.Dyn</c> nor the recovery assumption appears here at all —
    /// <c>pack</c> and <c>unpack</c> are the base class's interface to its own encoding.
    /// </para>
    /// </summary>
    public (string Iface, string Impl) EmitVtbl(
        IrClass c, IrClass parent,
        ImmutableArray<IrMethod> virtuals, ImmutableArray<IrMethod> overrides)
    {
        var parts = new Parts();
        Header(parts.Iface, Names.VtblModule(c.Name));
        Header(parts.Impl, Names.VtblModule(c.Name));

        var self = Names.ClassType(c.Name);
        var mod = Names.ClassModule(c.Name);
        var pMod = Names.ClassModule(parent.Name);
        var asBase = $"{mod}.{Names.ClassAsBase(c.Name, parent.Name)}";
        var pModel = $"{pMod}.{Names.ClassModel(parent.Name)}";
        var pObj = $"{pMod}.{Names.ClassObj(parent.Name)}";

        // F33: F21's meta-argument-defaulted permission binder does not match a vtable
        // field type, so every slot is eta-expanded at the pack site.
        var vtbl = new StringBuilder();
        vtbl.AppendLine($"let {Names.ClassVtblValue(c.Name)} : {pMod}.{Names.ClassVtbl(parent.Name)} = {{");
        vtbl.AppendLine($"  impl = {mod}.{self};");
        vtbl.AppendLine($"  inv = (fun (x: {mod}.{self}) ({Perm}: perm) ({Model}: {pModel}) ->" +
                        $" {asBase} x #{Perm} {Model});");
        foreach (var v in virtuals)
        {
            var o = overrides.FirstOrDefault(m => Member(m) == Member(v));
            if (o is null) continue;
            var moves = !v.IsReadOnly;
            var args = string.Concat(Value(v).Select(p => $" ({Names.Local(p.Name)}: {Types.Render(p.Type)})"));
            var pass = string.Concat(Value(v).Select(p => " " + Names.Local(p.Name)));
            var permB = moves ? "" : $" (#{Perm}: perm)";
            var permA = moves ? "" : $" #{Perm}";
            vtbl.AppendLine($"  {Names.VtblSlot(Member(v))} = (fun (x: {mod}.{self}){args}{permB}" +
                            $" (#{Model}: erased {pModel}) ->");
            // The slot's binder order is fixed by the vtable type; the implementation's is
            // fixed by R4.10, which threads the model binder before R4.11b's permission.
            // The eta-expansion is where the two meet, and it is the only place they have
            // to: neither side bends towards the other.
            vtbl.AppendLine($"    {Names.FunctionModule(o.Name)}.{Names.Function(o.Name)}" +
                            $" x{pass} #{Model}{permA});");
        }
        // R9.11. The leaf already has R3.10d's bodies; they are lifted to the base model by
        // the same `as_B` view every method goes through.
        vtbl.AppendLine($"  vshare = (fun (x: {mod}.{self}) (#{Perm}: perm) (#{Model}: erased {pModel}) ->");
        vtbl.AppendLine($"    {mod}.{Names.ClassAsBase(c.Name, parent.Name)}_share x #{Perm} #{Model});");
        vtbl.AppendLine($"  vgather = (fun (x: {mod}.{self}) ({Perm}: perm) (q: perm)" +
                        $" (#{Model}: erased {pModel}) (#{Names.Alt(Model)}: erased {pModel}) ->");
        vtbl.AppendLine($"    {mod}.{Names.ClassAsBase(c.Name, parent.Name)}_gather x {Perm} q" +
                        $" #{Model} #{Names.Alt(Model)});");
        vtbl.Append("}");
        parts.Private(vtbl.ToString());

        // R9.8. The object record is built at the *base's* type: the reference is made once,
        // at the root, and an upcast is a change of invariant and not of value. A client
        // names this to say *which* object it is holding, and needs nothing of what is in it.
        var objOf = $"({Names.ClassObjOf(c.Name)} x)";
        parts.Public($"{Names.ClassObjOf(c.Name)} (x: {mod}.{self}) : {pObj}",
            $"let {Names.ClassObjOf(c.Name)} (x: {mod}.{self}) : {pObj} =\n" +
            $"  {{ pkg = {Names.ClassVtblValue(c.Name)}; rep = x; sub = Dn.mkdyn () }}");

        var pInvAt = $"{pMod}.{Names.ClassInvAt(parent.Name)}";

        // R9.15a. The upcast, as a value. A C# reference conversion produces a reference,
        // and the name it is bound to is the one every later resource must be attached to,
        // so the ghost step and the rebinding are one operation and not two. It keeps the
        // index: dropping it is one `forget_impl` wherever the plain form is wanted, and
        // nothing recovers it once dropped, so the informative resource is what to hand back.
        parts.Code(
            $"fn {Names.UpcastToAt(c.Name, parent.Name)} (x: {mod}.{self})" +
            $" (#{Perm}: perm) (#{Model}: erased {pModel})\n" +
            $"  requires {asBase} x #{Perm} {Model}\n" +
            $"  returns  s: {pMod}.{Names.ClassType(parent.Name)}\n" +
            $"  ensures  {pInvAt} s (hide {objOf}) {Perm} {Model}",
            "\n{\n" +
            $"  rewrite ({asBase} x #{Perm} {Model})" +
            $" as ({objOf}.pkg.inv {objOf}.rep {Perm} {Model});\n" +
            $"  {pMod}.{Names.ClassPack(parent.Name)} {objOf} #{Perm} #{Model}\n" +
            "}");

        // R9.16. The checked downcast. Its precondition *is* the knowledge C# would test
        // for at runtime: the index names the object record, so the recovery `unpack`
        // performs is given the equation it asks for. The cast therefore cannot fail, not
        // because a runtime test is proved to succeed, but because only the casts whose
        // test is redundant can be written at all.
        var cRep = $"({Names.ClassObjOf(c.Name)} (reveal {Witness}))";
        parts.Code(
            $"fn {Names.DowncastFrom(c.Name, parent.Name)}" +
            $" (s: {pMod}.{Names.ClassType(parent.Name)}) (#{Witness}: erased {mod}.{self})" +
            $" (#{Perm}: perm) (#{Model}: erased {pModel})\n" +
            $"  requires {pInvAt} s (hide {cRep}) {Perm} {Model}\n" +
            $"  returns  r: {mod}.{self}\n" +
            $"  ensures  {asBase} r #{Perm} {Model} ** pure (r == reveal {Witness})",
            "\n{\n" +
            $"  let r = {pMod}.{Names.ClassUnpack(parent.Name)} {Names.ClassVtblValue(c.Name)}" +
            $" {Witness} (hide (Dn.mkdyn ())) s #{Perm} #{Model};\n" +
            $"  rewrite ({Names.ClassVtblValue(c.Name)}.inv r {Perm} {Model})" +
            $" as ({asBase} r #{Perm} {Model});\n" +
            "  r\n" +
            "}");

        return (parts.Iface.ToString(), parts.Impl.ToString());
    }

    /// <summary>
    /// R9.11. The leaf's share and gather, lifted from its own model to the base's. They
    /// are what the vtable's <c>vshare</c> and <c>vgather</c> slots are filled with.
    /// </summary>
    public string EmitLeafShareGather(IrClass c, IrClass parent)
    {
        var sb = new StringBuilder();
        var self = Names.ClassType(c.Name);
        var asBase = Names.ClassAsBase(c.Name, parent.Name);
        var pModel = $"{Names.ClassModule(parent.Name)}.{Names.ClassModel(parent.Name)}";
        var own = Names.ClassModel(c.Name);
        var inv = Names.ClassInv(c.Name);
        var half = $"({Perm} /. 2.0R)";
        var alt = Names.Alt(Model);

        sb.AppendLine();
        sb.AppendLine($"ghost fn {asBase}_share (this: {self}) (#{Perm}: perm) (#{Model}: erased {pModel})");
        sb.AppendLine($"  requires {asBase} this #{Perm} {Model}");
        sb.AppendLine($"  ensures  {asBase} this #{half} {Model} ** {asBase} this #{half} {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({asBase} this #{Perm} {Model});");
        sb.AppendLine($"  with own. assert ({inv} this #{Perm} own);");
        sb.AppendLine($"  {Names.ClassInvShare(c.Name)} this #{Perm} #own;");
        sb.AppendLine($"  fold ({asBase} this #{half} {Model});");
        sb.AppendLine($"  fold ({asBase} this #{half} {Model});");
        sb.AppendLine("}");
        sb.AppendLine();
        sb.AppendLine("[@@allow_ambiguous]");
        sb.AppendLine($"ghost fn {asBase}_gather (this: {self}) ({Perm}: perm) (q: perm)" +
                      $" (#{Model}: erased {pModel}) (#{alt}: erased {pModel})");
        sb.AppendLine($"  requires {asBase} this #{Perm} {Model} ** {asBase} this #q {alt}");
        sb.AppendLine($"  ensures  {asBase} this #({Perm} +. q) {Model} **" +
                      $" pure (reveal {Model} == reveal {alt})");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({asBase} this #{Perm} {Model});");
        sb.AppendLine($"  with own. assert ({inv} this #{Perm} own);");
        sb.AppendLine($"  unfold ({asBase} this #q {alt});");
        sb.AppendLine($"  with own2. assert ({inv} this #q own2);");
        sb.AppendLine($"  {Names.ClassInvGatherGen(c.Name)} this {Perm} q #own #own2;");
        sb.AppendLine($"  fold ({asBase} this #({Perm} +. q) {Model});");
        sb.AppendLine("}");
        return sb.ToString();
    }

    // =======================================================================
    // Shared helpers
    // =======================================================================

    private const string PostModel = "post_this";

    /// <summary>
    /// R9.3-adjacent, without the diagnostic: whether a virtual method has a slot. A
    /// subclass asks this about its ancestors' methods, which have already been checked and
    /// reported on where they were declared.
    /// </summary>
    public static bool Admissible(IrMethod v) =>
        Value(v).All(p => p.Mode == ParamMode.Value &&
                          p.Type is IrPrim { IsMachineInt: true } or IrPrim { Kind: PrimKind.Bool })
        && v.ReturnType is IrPrim;

    /// <summary>R9.3-adjacent: a virtual method takes and returns values only.</summary>
    public bool CheckVirtual(IrClass c, IrMethod v)
    {
        foreach (var p in Value(v))
        {
            if (p.Type is IrPrim { IsMachineInt: true } or IrPrim { Kind: PrimKind.Bool }
                && p.Mode == ParamMode.Value) continue;
            diagnostics.Error("PALCS0545", p.Loc,
                $"`{c.Name}.{Member(v)}` is `abstract` and takes `{p.Name}`, which is not a plain value. " +
                "A vtable slot's type is fixed by the base class, so every subclass would have to own " +
                "the same resource in the same way (doc/translation.md R9.9); only value parameters " +
                "have a reading that does not depend on the implementation.");
            return false;
        }
        if (v.ReturnType is IrPrim) return true;
        diagnostics.Error("PALCS0545", v.Loc,
            $"`{c.Name}.{Member(v)}` is `abstract` and returns `{v.ReturnType}`. A vtable slot returns a " +
            "value; returning a resource would make the slot's type depend on the implementation.");
        return false;
    }

    /// <summary>
    /// The member's own name within the class that <em>declared</em> it. R9.18: an
    /// inherited virtual keeps the name it was declared with all the way down, so that a
    /// subclass three levels away fills the slot the root named.
    /// </summary>
    private static string Member(IrMethod m) => Names.Member(m.Name, m.DeclaringClass!);

    /// <summary>The method's parameters other than the receiver.</summary>
    private static IEnumerable<IrParam> Value(IrMethod v) =>
        v.Parameters.Where(p => p.Name != Names.This);

    /// <summary>
    /// R9.7. The virtual method's contract, read at <paramref name="c"/>'s model. The
    /// receiver denotes the model binder, exactly as R4.10 makes it denote the model in an
    /// ordinary instance method's contract.
    /// </summary>
    /// <param name="c">The class whose model the contract is read at.</param>
    /// <param name="module">
    /// The class whose module the contract is being written into, when that is not
    /// <paramref name="c"/>. R9.18's derived slots state a *parent's* contract inside a
    /// *subclass's* module, and a name is qualified or not according to where it is
    /// written, not according to whose model it is about.
    /// </param>
    private (string Pre, string Post) Contract(
        IrClass c, IrMethod v, string model, out bool moves, IrClass? module = null)
    {
        moves = !v.IsReadOnly;
        var type = new IrClassType(c.Name);
        var here = (module ?? c).Name;
        var pre = new SpecScope { DefiningClass = here };
        pre.Bind(Names.This, new Term($"(reveal {model})", TermKind.Math, type));

        var post = new SpecScope
        {
            Pre = pre,
            DefiningClass = here,
            ResultTerm = Ret,
            ResultKind = MethodPlan.KindOf(v.ReturnType),
        };
        post.Bind(Names.This, moves
            ? new Term(PostModel, TermKind.Math, type)
            : new Term($"(reveal {model})", TermKind.Math, type));

        var requires = SpecEmitter.Conjunction(v.Requires.Select(r => spec.AsProp(spec.Emit(r, pre))));
        var ensures = SpecEmitter.Conjunction(
            v.Ensures.Concat(v.Preserves).Select(e => spec.AsProp(spec.Emit(e, post))));
        var req = v.Requires.Length == 0 ? "" : requires;
        var ens = v.Ensures.Length + v.Preserves.Length == 0 ? "" : ensures;
        // R4.8, unchanged: a Pulse `ensures` is checked without the `requires` in scope,
        // so the precondition is restated as a hypothesis. A vtable slot is a method type
        // and gets the same treatment — otherwise the slot and the implementation that
        // fills it would state the same C# contract two different ways.
        return (req, MethodPlan.UnderPrecondition([req], [ens]).Single());
    }

    private static string Pure(string clause) => clause.Length == 0 ? "" : $" ** pure ({clause})";

    /// <summary>
    /// R3.9d. The refined model type. Shared with the M2 class emitter rather than copied,
    /// so that an abstract class and a leaf cannot drift apart on what a model is.
    /// </summary>
    public void EmitModelType(StringBuilder sb, IrClass c)
    {
        var modelScope = new SpecScope
        {
            ResultTerm = Model,
            ResultKind = MethodPlan.KindOf(c.ModelType),
            DefiningClass = c.Name,
        };
        var pred = c.ModelRefinements.Length == 0
            ? "True"
            : SpecEmitter.Conjunction(c.ModelRefinements.Select(r => spec.AsProp(spec.Emit(r, modelScope))));
        // R15.2. The refinement is a predicate on the model, so it takes the parameter
        // implicitly like every other non-type definition; the model type is a type
        // definition, so it takes it explicitly.
        var tb = TypeBinders.Of(c);
        sb.AppendLine($"let {Names.ClassModelPred(c.Name)}{tb.Implicit} " +
                      $"({Model}: {Types.Render(c.ModelType)}) : prop =");
        sb.AppendLine($"  {pred}");
        sb.AppendLine();
        sb.AppendLine($"type {Names.ClassModel(c.Name)}{tb.Explicit} = " +
                      $"{Model}: {Types.Render(c.ModelType)} {{ {Names.ClassModelPred(c.Name)} {Model} }}");
        sb.AppendLine();
    }

    /// <summary>R3.9c. Each <c>[Spec]</c> member as a pure function of the model.</summary>
    public void EmitObservations(StringBuilder sb, IrClass c)
    {
        foreach (var o in c.Observations)
        {
            var obsScope = new SpecScope { DefiningClass = c.Name };
            obsScope.Bind(c.ModelMember, new Term(Model, MethodPlan.KindOf(c.ModelType), c.ModelType));
            var (ret, text) = o.ReturnType switch
            {
                IrPrim { Kind: PrimKind.Bool } => ("prop", spec.AsProp(spec.Emit(o.Body, obsScope))),
                IrPrim { IsMachineInt: true } => ("int", spec.Math(o.Body, obsScope)),
                _ => (Types.Render(o.ReturnType), spec.Emit(o.Body, obsScope).Text),
            };
            var tb = TypeBinders.Of(c);
            sb.AppendLine($"let {Names.Observation(c.Name, o.Name)}{tb.Implicit} " +
                          $"({Model}: {tb.App(Names.ClassModel(c.Name))}) : {ret} =");
            sb.AppendLine($"  {text}");
            sb.AppendLine();
        }
    }

    private static void Header(StringBuilder sb, string module)
    {
        sb.AppendLine($"module {module}");
        sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        sb.AppendLine(Preamble.Opens);
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        sb.AppendLine("module T = FStar.Tactics");
        sb.AppendLine("module Dn = FStar.Dyn");
        sb.AppendLine("module CAs = Pulse.Lib.CSharp.Assumptions");
        sb.AppendLine();
    }
}
