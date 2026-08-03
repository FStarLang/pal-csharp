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
    private const string Perm = "p";
    private const string Model = "m";
    private const string Obj = "o";
    private const string Ret = "ret";

    /// <summary>The permission a mutating slot demands: all of it.</summary>
    private const string Full = "1.0R";

    // =======================================================================
    // The abstract class
    // =======================================================================

    /// <summary>
    /// R9.9. The whole of an abstract class: the model, the observations, the vtable, the
    /// object record, the reference type, the two invariants, and a dispatching wrapper
    /// per virtual method.
    /// </summary>
    public string EmitAbstract(IrClass c, ImmutableArray<IrMethod> virtuals)
    {
        var sb = new StringBuilder();
        Header(sb, Names.ClassModule(c.Name));

        // R9.9. A slot's type is fixed by the base class, so a virtual method whose
        // signature has no implementation-independent reading has no slot. Checked once,
        // here, so that a refused method is absent from the vtable and from dispatch alike.
        var slots = virtuals.Where(v => CheckVirtual(c, v)).ToImmutableArray();
        var model = Names.ClassModel(c.Name);
        EmitModelType(sb, c);
        EmitObservations(sb, c);

        // R9.9. One field per virtual method, at *this* class's model, plus the two
        // things a vtable must carry that no C# declaration mentions: the representation
        // type, and how a permission splits over it.
        sb.AppendLine($"noeq type {Names.ClassVtbl(c.Name)} = {{");
        sb.AppendLine("  impl : Type0;");
        sb.AppendLine();
        sb.AppendLine($"  inv : impl -> perm -> {model} -> slprop;");
        foreach (var v in slots)
        {
            sb.AppendLine();
            sb.AppendLine($"  {Names.VtblSlot(Member(c, v))} : ({SlotType(c, v)});");
        }
        // R9.11. R3.10d emits share and gather per class because their proofs recurse into
        // the class's own fields. Behind a dyn there is no structure to recurse into, so
        // they become dispatched operations and the leaf supplies the bodies it already
        // has. They are `stt_ghost`, which is why aliasing a `Shape` stays free at runtime.
        sb.AppendLine();
        sb.AppendLine($"  vshare : (x: impl -> #{Perm}: perm -> #{Model}: erased {model} ->");
        sb.AppendLine("            stt_ghost unit emp_inames");
        sb.AppendLine($"              (inv x {Perm} {Model})");
        sb.AppendLine($"              (fun _ -> inv x ({Perm} /. 2.0R) {Model} ** inv x ({Perm} /. 2.0R) {Model}));");
        sb.AppendLine();
        sb.AppendLine($"  vgather : (x: impl -> {Perm}: perm -> q: perm ->" +
                      $" #{Model}: erased {model} -> #{Names.Alt(Model)}: erased {model} ->");
        sb.AppendLine("             stt_ghost unit emp_inames");
        sb.AppendLine($"               (inv x {Perm} {Model} ** inv x q {Names.Alt(Model)})");
        sb.AppendLine($"               (fun _ -> inv x ({Perm} +. q) {Model} **" +
                      $" pure (reveal {Model} == reveal {Names.Alt(Model)})));");
        sb.AppendLine("}");
        sb.AppendLine();

        var obj = Names.ClassObj(c.Name);
        var at = Names.ClassAt(c.Name);
        var inv = Names.ClassInv(c.Name);
        var invAt = Names.ClassInvAt(c.Name);
        var self = Names.ClassType(c.Name);

        // F28: a vtable together with a value of *its* implementation type is far too big
        // to live in a heap cell or an array, so F29 promotes it into `dyn`, which is
        // `Type0` and therefore boxable, array-able, and admissible as a field. R9.8: the
        // dyn is what a variable of this static type denotes.
        sb.AppendLine($"noeq type {obj} = {{ pkg: {Names.ClassVtbl(c.Name)}; rep: pkg.impl }}");
        sb.AppendLine();
        sb.AppendLine($"let {self} : Type0 = Dn.dyn");
        sb.AppendLine();

        // F34: named apart from the invariant so that a `fold` can be handed an explicit
        // witness for the existential.
        sb.AppendLine($"let {at} (o: {obj}) ({Perm}: perm) ({Model}: {model}) : slprop =" +
                      $" o.pkg.inv o.rep {Perm} {Model}");
        sb.AppendLine();

        // R9.9. The same signature an M2 class invariant has (§3.4), which is why a client
        // of a hierarchy needs no new rules: R4.5's model binders, R4.10's fold/unfold
        // bracket, R3.10b's nested objects and R5.12's loops all apply unchanged.
        sb.AppendLine($"let {inv} (s: {self}) (#[T.exact (`{Full})] {Perm}: perm)" +
                      $" ({Model}: {model}) : slprop =");
        sb.AppendLine($"  exists* ({Obj}: {obj}). pure (s == Dn.mkdyn {Obj}) **" +
                      $" {at} {Obj} {Perm} {Model}");
        sb.AppendLine();

        // R9.10. The primitive form, with the object record named. `gather` forces it —
        // two views of one object otherwise unfold to separate witnesses related only by
        // `s == mkdyn o1` and `s == mkdyn o2`, and equating those is injectivity of
        // `mkdyn`, which is Cantor-inconsistent. A checked downcast needs the same index.
        sb.AppendLine($"let {invAt} (s: {self}) ({Obj}: erased {obj}) ({Perm}: perm)" +
                      $" ({Model}: {model}) : slprop =");
        sb.AppendLine($"  pure (s == Dn.mkdyn (reveal {Obj})) ** {at} {Obj} {Perm} {Model}");
        sb.AppendLine();

        // R9.10. Forgetting is one ghost step, and irreversible: recovering the index from
        // the plain invariant would again be injectivity of `mkdyn`.
        sb.AppendLine($"ghost fn {Names.ClassForgetImpl(c.Name)} (s: {self}) ({Obj}: erased {obj})" +
                      $" (#{Perm}: perm) (#{Model}: erased {model})");
        sb.AppendLine($"  requires {invAt} s {Obj} {Perm} {Model}");
        sb.AppendLine($"  ensures  {inv} s #{Perm} {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({invAt} s {Obj} {Perm} {Model});");
        sb.AppendLine($"  fold ({inv} s #{Perm} {Model});");
        sb.AppendLine("}");
        sb.AppendLine();

        EmitShareGather(sb, c);
        foreach (var v in slots) EmitDispatch(sb, c, v);

        return sb.ToString();
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
    private void EmitDispatch(StringBuilder sb, IrClass c, IrMethod v)
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
        sb.AppendLine($"fn {Names.DispatchAt(c.Name, Member(c, v))} (s: {self}){binders}" +
                      $" (#{Obj}: erased {obj}){permBinder} (#{Model}: erased {model})");
        sb.AppendLine($"  requires {invAt} s {Obj} {perm} {Model}{Pure(pre)}");
        sb.Append(returns);
        sb.AppendLine(moves
            ? $"  ensures  exists* {PostModel}. {invAt} s {Obj} {perm} {PostModel}{Pure(post)}"
            : $"  ensures  {invAt} s {Obj} {perm} {Model}{Pure(post)}");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({invAt} s {Obj} {perm} {Model});");
        // R9.13. The one assumption: the object header faithfully records what was stored.
        sb.AppendLine($"  let ob = CAs.recover #{obj} #{Obj} s;");
        sb.AppendLine($"  rewrite ({at} {Obj} {perm} {Model}) as ({at} ob {perm} {Model});");
        sb.AppendLine($"  unfold ({at} ob {perm} {Model});");
        // F31: a stored Pulse computation must be let-bound before it is applied.
        sb.AppendLine($"  let f = ob.pkg.{Names.VtblSlot(Member(c, v))};");
        var call = $"f ob.rep{args}{(moves ? "" : $" #{Perm}")} #{Model};";
        if (moves)
        {
            sb.AppendLine($"  {call}");
            sb.AppendLine($"  with {PostModel}. assert (ob.pkg.inv ob.rep {perm} {PostModel});");
            sb.AppendLine($"  fold ({at} ob {perm} {PostModel});");
            sb.AppendLine($"  rewrite ({at} ob {perm} {PostModel}) as ({at} {Obj} {perm} {PostModel});");
            sb.AppendLine($"  fold ({invAt} s {Obj} {perm} {PostModel});");
        }
        else
        {
            sb.AppendLine($"  let v = {call}");
            sb.AppendLine($"  fold ({at} ob {perm} {Model});");
            sb.AppendLine($"  rewrite ({at} ob {perm} {Model}) as ({at} {Obj} {perm} {Model});");
            sb.AppendLine($"  fold ({invAt} s {Obj} {perm} {Model});");
            if (v.ReturnType is not IrPrim { Kind: PrimKind.Void }) sb.AppendLine("  v");
        }
        sb.AppendLine("}");
        sb.AppendLine();

        // R9.10. The plain form is the indexed one composed with forgetting, so there is
        // one dispatching body per method and not two.
        sb.AppendLine($"fn {Names.Dispatch(c.Name, Member(c, v))} (s: {self}){binders}" +
                      $"{permBinder} (#{Model}: erased {model})");
        sb.AppendLine($"  requires {inv} s #{perm} {Model}{Pure(pre)}");
        sb.Append(returns);
        sb.AppendLine(moves
            ? $"  ensures  exists* {PostModel}. {inv} s #{perm} {PostModel}{Pure(post)}"
            : $"  ensures  {inv} s #{perm} {Model}{Pure(post)}");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({inv} s #{perm} {Model});");
        sb.AppendLine($"  with {Obj}. assert ({at} {Obj} {perm} {Model});");
        sb.AppendLine($"  fold ({invAt} s (hide {Obj}) {perm} {Model});");
        var inner = $"{Names.DispatchAt(c.Name, Member(c, v))} s{args} #(hide {Obj})" +
                    $"{(moves ? "" : $" #{Perm}")} #{Model};";
        if (moves)
        {
            sb.AppendLine($"  {inner}");
            sb.AppendLine($"  with {PostModel}. assert ({invAt} s (hide {Obj}) {perm} {PostModel});");
            sb.AppendLine($"  {Names.ClassForgetImpl(c.Name)} s (hide {Obj}) #{perm} #{PostModel};");
        }
        else
        {
            sb.AppendLine($"  let v = {inner}");
            sb.AppendLine($"  {Names.ClassForgetImpl(c.Name)} s (hide {Obj}) #{perm} #{Model};");
            if (v.ReturnType is not IrPrim { Kind: PrimKind.Void }) sb.AppendLine("  v");
        }
        sb.AppendLine("}");
        sb.AppendLine();
    }

    /// <summary>R9.11. Dispatched sharing and gathering, both ghost.</summary>
    private static void EmitShareGather(StringBuilder sb, IrClass c)
    {
        var model = Names.ClassModel(c.Name);
        var self = Names.ClassType(c.Name);
        var obj = Names.ClassObj(c.Name);
        var at = Names.ClassAt(c.Name);
        var inv = Names.ClassInv(c.Name);
        var invAt = Names.ClassInvAt(c.Name);
        var alt = Names.Alt(Model);
        var half = $"({Perm} /. 2.0R)";

        sb.AppendLine($"ghost fn {Names.ClassInvShare(c.Name)}_at (s: {self}) ({Obj}: erased {obj})" +
                      $" (#{Perm}: perm) (#{Model}: erased {model})");
        sb.AppendLine($"  requires {invAt} s {Obj} {Perm} {Model}");
        sb.AppendLine($"  ensures  {invAt} s {Obj} {half} {Model} ** {invAt} s {Obj} {half} {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({invAt} s {Obj} {Perm} {Model});");
        sb.AppendLine($"  unfold ({at} {Obj} {Perm} {Model});");
        sb.AppendLine($"  let f = {Obj}.pkg.vshare;");
        sb.AppendLine($"  f {Obj}.rep #{Perm} #{Model};");
        sb.AppendLine($"  fold ({at} {Obj} {half} {Model});");
        sb.AppendLine($"  fold ({at} {Obj} {half} {Model});");
        sb.AppendLine($"  fold ({invAt} s {Obj} {half} {Model});");
        sb.AppendLine($"  fold ({invAt} s {Obj} {half} {Model});");
        sb.AppendLine("}");
        sb.AppendLine();

        sb.AppendLine($"ghost fn {Names.ClassInvShare(c.Name)} (s: {self})" +
                      $" (#{Perm}: perm) (#{Model}: erased {model})");
        sb.AppendLine($"  requires {inv} s #{Perm} {Model}");
        sb.AppendLine($"  ensures  {inv} s #{half} {Model} ** {inv} s #{half} {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({inv} s #{Perm} {Model});");
        sb.AppendLine($"  with {Obj}. assert ({at} {Obj} {Perm} {Model});");
        sb.AppendLine($"  fold ({invAt} s (hide {Obj}) {Perm} {Model});");
        sb.AppendLine($"  {Names.ClassInvShare(c.Name)}_at s (hide {Obj}) #{Perm} #{Model};");
        sb.AppendLine($"  {Names.ClassForgetImpl(c.Name)} s (hide {Obj}) #{half} #{Model};");
        sb.AppendLine($"  {Names.ClassForgetImpl(c.Name)} s (hide {Obj}) #{half} #{Model};");
        sb.AppendLine("}");
        sb.AppendLine();

        // Only the *indexed* gather exists. The unindexed one is unprovable: two views of
        // one object unfold to separate witnesses related only through `mkdyn`, and
        // equating them is the injectivity `ShapeHierarchy.fst` §3 pins as unavailable.
        sb.AppendLine("[@@allow_ambiguous]");
        sb.AppendLine($"ghost fn {Names.ClassInvGather(c.Name)}_at (s: {self}) ({Obj}: erased {obj})" +
                      $" ({Perm}: perm) (q: perm) (#{Model}: erased {model}) (#{alt}: erased {model})");
        sb.AppendLine($"  requires {invAt} s {Obj} {Perm} {Model} ** {invAt} s {Obj} q {alt}");
        sb.AppendLine($"  ensures  {invAt} s {Obj} ({Perm} +. q) {Model} **" +
                      $" pure (reveal {Model} == reveal {alt})");
        sb.AppendLine("{");
        sb.AppendLine($"  unfold ({invAt} s {Obj} {Perm} {Model});");
        sb.AppendLine($"  unfold ({invAt} s {Obj} q {alt});");
        sb.AppendLine($"  unfold ({at} {Obj} {Perm} {Model});");
        sb.AppendLine($"  unfold ({at} {Obj} q {alt});");
        sb.AppendLine($"  let g = {Obj}.pkg.vgather;");
        sb.AppendLine($"  g {Obj}.rep {Perm} q #{Model} #{alt};");
        sb.AppendLine($"  fold ({at} {Obj} ({Perm} +. q) {Model});");
        sb.AppendLine($"  fold ({invAt} s {Obj} ({Perm} +. q) {Model});");
        sb.AppendLine("}");
        sb.AppendLine();
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

        // R9.6. The base's model as a function of this class's — the `override` of the
        // base's [Model] member, and nothing else in C# has to be written to get it.
        var scope = new SpecScope { DefiningClass = c.Name };
        scope.Bind(c.ModelMember, new Term(Model, MethodPlan.KindOf(c.ModelType), c.ModelType));
        var forget = c.ForgetBody is null
            ? Model
            : MethodPlan.KindOf(parent.ModelType) == TermKind.Math
                ? spec.Math(c.ForgetBody, scope)
                : spec.Emit(c.ForgetBody, scope).Text;

        sb.AppendLine();
        sb.AppendLine($"let {Names.ClassForget(c.Name)} ({Model}: {own}) : {pModel} =");
        sb.AppendLine($"  {forget}");
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
    /// R9.14. The vtable <em>value</em>, the object record, and the upcast. It is a module
    /// of its own because it mentions every method module, and the constructor's module
    /// mentions it.
    /// </summary>
    public string EmitVtbl(
        IrClass c, IrClass parent,
        ImmutableArray<IrMethod> virtuals, ImmutableArray<IrMethod> overrides)
    {
        var sb = new StringBuilder();
        Header(sb, Names.VtblModule(c.Name));

        var self = Names.ClassType(c.Name);
        var mod = Names.ClassModule(c.Name);
        var pMod = Names.ClassModule(parent.Name);
        var asBase = $"{mod}.{Names.ClassAsBase(c.Name, parent.Name)}";
        var pModel = $"{pMod}.{Names.ClassModel(parent.Name)}";

        // F33: F21's meta-argument-defaulted permission binder does not match a vtable
        // field type, so every slot is eta-expanded at the pack site.
        sb.AppendLine($"let {Names.ClassVtblValue(c.Name)} : {pMod}.{Names.ClassVtbl(parent.Name)} = {{");
        sb.AppendLine($"  impl = {mod}.{self};");
        sb.AppendLine($"  inv = (fun (x: {mod}.{self}) ({Perm}: perm) ({Model}: {pModel}) ->" +
                      $" {asBase} x #{Perm} {Model});");
        foreach (var v in virtuals)
        {
            var o = overrides.FirstOrDefault(m => Member(c, m) == Member(parent, v));
            if (o is null) continue;
            var moves = !v.IsReadOnly;
            var args = string.Concat(Value(v).Select(p => $" ({Names.Local(p.Name)}: {Types.Render(p.Type)})"));
            var pass = string.Concat(Value(v).Select(p => " " + Names.Local(p.Name)));
            var permB = moves ? "" : $" (#{Perm}: perm)";
            var permA = moves ? "" : $" #{Perm}";
            sb.AppendLine($"  {Names.VtblSlot(Member(parent, v))} = (fun (x: {mod}.{self}){args}{permB}" +
                          $" (#{Model}: erased {pModel}) ->");
            // The slot's binder order is fixed by the vtable type; the implementation's is
            // fixed by R4.10, which threads the model binder before R4.11b's permission.
            // The eta-expansion is where the two meet, and it is the only place they have
            // to: neither side bends towards the other.
            sb.AppendLine($"    {Names.FunctionModule(o.Name)}.{Names.Function(o.Name)}" +
                          $" x{pass} #{Model}{permA});");
        }
        // R9.11. The leaf already has R3.10d's bodies; they are lifted to the base model by
        // the same `as_B` view every method goes through.
        sb.AppendLine($"  vshare = (fun (x: {mod}.{self}) (#{Perm}: perm) (#{Model}: erased {pModel}) ->");
        sb.AppendLine($"    {mod}.{Names.ClassAsBase(c.Name, parent.Name)}_share x #{Perm} #{Model});");
        sb.AppendLine($"  vgather = (fun (x: {mod}.{self}) ({Perm}: perm) (q: perm)" +
                      $" (#{Model}: erased {pModel}) (#{Names.Alt(Model)}: erased {pModel}) ->");
        sb.AppendLine($"    {mod}.{Names.ClassAsBase(c.Name, parent.Name)}_gather x {Perm} q" +
                      $" #{Model} #{Names.Alt(Model)});");
        sb.AppendLine("}");
        sb.AppendLine();

        // R9.8. The object record is built at the *base's* type: the dyn is made once, at
        // the root, and an upcast is a change of invariant and not of value.
        sb.AppendLine($"let {Names.ClassObjOf(c.Name)} (x: {mod}.{self}) : {pMod}.{Names.ClassObj(parent.Name)} =");
        sb.AppendLine($"  {{ pkg = {Names.ClassVtblValue(c.Name)}; rep = x }}");
        sb.AppendLine();

        // R9.15. The upcast: a ghost fold, at the index and then plain.
        var pAt = $"{pMod}.{Names.ClassAt(parent.Name)}";
        var pInvAt = $"{pMod}.{Names.ClassInvAt(parent.Name)}";
        var made = $"(Dn.mkdyn ({Names.ClassObjOf(c.Name)} x))";
        sb.AppendLine($"ghost fn {Names.UpcastAt(c.Name)} (x: {mod}.{self}) (#{Perm}: perm)" +
                      $" (#{Model}: erased {pModel})");
        sb.AppendLine($"  requires {asBase} x #{Perm} {Model}");
        sb.AppendLine($"  ensures  {pInvAt} {made} (hide ({Names.ClassObjOf(c.Name)} x)) {Perm} {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  rewrite ({asBase} x #{Perm} {Model})" +
                      $" as ({pAt} ({Names.ClassObjOf(c.Name)} x) {Perm} {Model});");
        sb.AppendLine($"  fold ({pInvAt} {made} (hide ({Names.ClassObjOf(c.Name)} x)) {Perm} {Model});");
        sb.AppendLine("}");
        sb.AppendLine();
        sb.AppendLine($"ghost fn {Names.Upcast(c.Name)} (x: {mod}.{self}) (#{Perm}: perm)" +
                      $" (#{Model}: erased {pModel})");
        sb.AppendLine($"  requires {asBase} x #{Perm} {Model}");
        sb.AppendLine($"  ensures  {pMod}.{Names.ClassInv(parent.Name)} {made} #{Perm} {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  {Names.UpcastAt(c.Name)} x #{Perm} #{Model};");
        sb.AppendLine($"  {pMod}.{Names.ClassForgetImpl(parent.Name)} {made}" +
                      $" (hide ({Names.ClassObjOf(c.Name)} x)) #{Perm} #{Model};");
        sb.AppendLine("}");
        sb.AppendLine();

        // R9.15. The value form. A C# reference conversion produces a reference, and the
        // name it is bound to is the one every later resource must be attached to, so the
        // ghost step and the rebinding are one operation and not two.
        sb.AppendLine($"fn {Names.UpcastTo(c.Name, parent.Name)} (x: {mod}.{self})" +
                      $" (#{Perm}: perm) (#{Model}: erased {pModel})");
        sb.AppendLine($"  requires {asBase} x #{Perm} {Model}");
        sb.AppendLine($"  returns  s: {pMod}.{Names.ClassType(parent.Name)}");
        sb.AppendLine($"  ensures  {pMod}.{Names.ClassInv(parent.Name)} s #{Perm} {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  {Names.Upcast(c.Name)} x #{Perm} #{Model};");
        sb.AppendLine($"  {made}");
        sb.AppendLine("}");
        return sb.ToString();
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

    /// <summary>R9.3-adjacent: a virtual method takes and returns values only.</summary>
    public bool CheckVirtual(IrClass c, IrMethod v)
    {
        foreach (var p in Value(v))
        {
            if (p.Type is IrPrim { IsMachineInt: true } or IrPrim { Kind: PrimKind.Bool }
                && p.Mode == ParamMode.Value) continue;
            diagnostics.Error("PALCS0545", p.Loc,
                $"`{c.Name}.{Member(c, v)}` is `abstract` and takes `{p.Name}`, which is not a plain value. " +
                "A vtable slot's type is fixed by the base class, so every subclass would have to own " +
                "the same resource in the same way (doc/translation.md R9.9); only value parameters " +
                "have a reading that does not depend on the implementation.");
            return false;
        }
        if (v.ReturnType is IrPrim) return true;
        diagnostics.Error("PALCS0545", v.Loc,
            $"`{c.Name}.{Member(c, v)}` is `abstract` and returns `{v.ReturnType}`. A vtable slot returns a " +
            "value; returning a resource would make the slot's type depend on the implementation.");
        return false;
    }

    /// <summary>The member's own name within its class.</summary>
    private static string Member(IrClass c, IrMethod m) => Names.Member(m.Name, c.Name);

    /// <summary>The method's parameters other than the receiver.</summary>
    private static IEnumerable<IrParam> Value(IrMethod v) =>
        v.Parameters.Where(p => p.Name != Names.This);

    /// <summary>
    /// R9.7. The virtual method's contract, read at <paramref name="c"/>'s model. The
    /// receiver denotes the model binder, exactly as R4.10 makes it denote the model in an
    /// ordinary instance method's contract.
    /// </summary>
    private (string Pre, string Post) Contract(IrClass c, IrMethod v, string model, out bool moves)
    {
        moves = !v.IsReadOnly;
        var type = new IrClassType(c.Name);
        var pre = new SpecScope { DefiningClass = c.Name };
        pre.Bind(Names.This, new Term($"(reveal {model})", TermKind.Math, type));

        var post = new SpecScope
        {
            Pre = pre,
            DefiningClass = c.Name,
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
        sb.AppendLine($"let {Names.ClassModelPred(c.Name)} ({Model}: {Types.Render(c.ModelType)}) : prop =");
        sb.AppendLine($"  {pred}");
        sb.AppendLine();
        sb.AppendLine($"type {Names.ClassModel(c.Name)} = " +
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
            sb.AppendLine($"let {Names.Observation(c.Name, o.Name)} " +
                          $"({Model}: {Names.ClassModel(c.Name)}) : {ret} =");
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
