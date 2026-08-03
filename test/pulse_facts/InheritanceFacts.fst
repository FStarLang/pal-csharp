module InheritanceFacts

/// Toolchain facts that any translation of C# *subtype polymorphism* -- interfaces
/// and virtual methods -- has to be built on. These are F28-F34 of doc/translation.md.
///
/// Like PulseFacts, StructFacts and ObjectFacts, these are NOT translation targets and
/// NOT golden files. Nothing in the emitter produces these shapes yet: doc/translation.md
/// section 0 requires the facts to be probed and pinned *before* a rule is written, and
/// this file is that step for inheritance. It exists so that the design recorded in
/// section 8 rests on measured behaviour rather than on plausibility.
///
/// The running example is a `Shape` with an abstract `Area()`, implemented by a `Circle`
/// (whose model is *larger* than Shape's -- it has a radius) and by a `Square` (whose
/// representation is not even the same shape of record). That is the smallest example
/// that exercises every hard part at once: a value whose implementation type is not
/// known statically, a model that grows along the hierarchy, and a heterogeneous
/// container.

open Pulse

module A = Pulse.Lib.Array
module B = Pulse.Lib.Box
module Dn = FStar.Dyn
module I32 = FStar.Int32
module Seq = FStar.Seq
module T = FStar.Tactics

#lang-pulse

/// The pure model of the hierarchy, shared by every implementation: a shape is known
/// by its area alone.
let shape__model = int

/// The vtable. An implementation type, the invariant relating it to the model, and one
/// entry per virtual method. This is the `t_C` of the design sketch.
noeq type t_shape = {
  impl : Type0;
  inv  : impl -> perm -> shape__model -> slprop;
  area : (x:impl -> #p:perm -> #m:erased shape__model ->
          stt I32.t (inv x p m) (fun v -> inv x p m ** pure (I32.v v == reveal m)));
}

/// A fully applied object: a vtable together with a value of *its* implementation type.
/// This dependent pair is what a variable of static type `Shape` denotes.
noeq type shape__obj = { pkg: t_shape; rep: pkg.impl }


// ---------------------------------------------------------------------------------
// F28: the vtable lives far above Type0, so it is not a Box payload.
// ---------------------------------------------------------------------------------

/// F28: `slprop : Type u#4` (Pulse.Lib.Core.fsti), so a record with an invariant field
///      and `stt`-typed method fields lives in universe 4 -- not, as one might guess,
///      in universe 1 because of its `impl : Type0` field. `Pulse.Lib.Box.box` requires
///      a `Type0` payload (`val box ([@@@strictly_positive] a:Type0) : Type0`), so the
///      dependent pair cannot be stored in a heap cell.
///
///      This is the fact that decides the whole encoding. Every pal-csharp object is
///      `B.box class_C__raw` (R3.7), so if a `Shape` cannot be a Box payload then it
///      cannot be a field of another class, and `Shape[]` cannot be allocated by
///      `Pulse.Lib.CSharp.Array` either -- that library is over `Pulse.Lib.SmallType`.
///      `class Outer { Shape s; }` and `List<Shape>` are the two constructs at stake.

let slprop_is_universe_four : Type u#4 = slprop

[@@expect_failure]
let vtable_is_not_boxable : Type0 = B.box shape__obj

/// F28b: the restriction really is `Box`'s, not Pulse's in general -- a *plain*
///       `Pulse.Lib.Array` is universe polymorphic and both its type and its ownership
///       predicate accept a high-universe element type. It is the C# array library
///       (SmallType) and the heap cell that force Type0. Recording this keeps a future
///       rule from blaming the wrong component.

let vtable_array_type_is_fine = A.array shape__obj
let vtable_array_ownership_is_fine (a: A.array shape__obj) (s: Seq.seq shape__obj) : slprop =
  A.pts_to a s


// ---------------------------------------------------------------------------------
// F29: FStar.Dyn lowers any universe to Type0.
// ---------------------------------------------------------------------------------

/// F29: `FStar.Dyn.dyn : Type0`, and `mkdyn : #a:Type u#a -> a -> dyn` is universe
///      polymorphic, so a `Shape` variable can be represented by the *promotion* of its
///      dependent pair. Concretely `dyn = unit -> Dv value_type_bundle`: the lowering is
///      the standard thunking trick, the same one PulseCore uses for its own semantics
///      (`PulseCore.InstantiatedSemantics.lower (t:Type u#a) : Type0 = unit -> Dv t`).
///
///      With `Shape` a Type0, F28's two casualties come back: a Shape is a Box payload,
///      an array element, and a field of another class's representation record.

let shape : Type0 = Dn.dyn

/// named separately from `shape__inv` so that a `fold` can be handed an explicit
/// witness -- see F34.
let shape__at (o: shape__obj) (p: perm) (m: shape__model) : slprop = o.pkg.inv o.rep p m

let shape__inv (s: shape) (#[T.exact (`1.0R)] p: perm) (m: shape__model) : slprop =
  exists* (o: shape__obj). pure (s == Dn.mkdyn o) ** shape__at o p m

let shape_is_boxable   : Type0 = B.box shape
let shape_is_arrayable : Type0 = A.array shape
let shape_array_is_ownable (a: A.array shape) (s: Seq.seq shape) : slprop = A.pts_to a s
noeq type outer__raw = { fld_s: shape; fld_n: I32.t }
let shape_is_a_field : Type0 = B.box outer__raw


// ---------------------------------------------------------------------------------
// F30: recovering the object costs exactly one axiom.
// ---------------------------------------------------------------------------------

/// F30: `FStar.Dyn.undyn` cannot be called from Pulse at all: it is in `Dv`, and a Pulse
///      `let` of a non-stt term admits only Tot and Ghost. So the lowering is unusable
///      as shipped.
///
///      Worse, no round-trip law can be *proved*. `undyn` returns in `Dv` and results of
///      `Dv` computations cannot be equated in specifications, so `undyn (mkdyn x) == x`
///      is not merely absent from FStar.Dyn.fsti, it is unstatable there.
///
///      This matters because separation-logic ownership is about a *particular* value,
///      not a type. The context holds `shape__at o p m` for the `o` that was stored;
///      `undyn` yields some `ob : shape__obj` of the right type; without `ob == o` the
///      resource cannot be rewritten onto `ob` and the method call has no permission to
///      match against. A well-typed reference that owns nothing is useless -- the proof
///      does not fail conservatively, it does not go through at all.
///
///      The cost is therefore one assumption, discharged by the platform rather than by
///      F*: *the CLR object header faithfully records the dynamic type*, so recovering
///      an object from a reference yields the object that was stored. That is exactly
///      the guarantee C# virtual dispatch already relies on, and it belongs alongside
///      the other platform axioms in Pulse.Lib.CSharp.Assumptions. Stated as an `stt`
///      it is usable from Pulse and it carries the missing equation.

[@@expect_failure]
fn undyn_is_not_callable_from_pulse (s: shape) (#p: perm) (#m: erased shape__model)
  preserves shape__inv s #p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (shape__inv s #p m);
  with o. assert (shape__at o p m);
  let ob = Dn.undyn #shape__obj s;
  admit()
}

assume
val undyn_stt (#a: Type u#a) (#x: erased a) (d: Dn.dyn { d == Dn.mkdyn (reveal x) })
  : stt a emp (fun y -> pure (y == reveal x))


// ---------------------------------------------------------------------------------
// F30b: the axiom must be stated in `stt`, not `stt_div`, and that is what makes it
//       an assumption rather than a triviality.
// ---------------------------------------------------------------------------------

/// F30b: Pulse has two computation types. `stt` is termination-checked; `stt_div` is
///       not, and the surface syntax for it is `divergent fn`. In the pinned toolchain
///       `hide_div : (unit -> Dv (stt_div a pre post)) -> stt_div a pre post` lands in
///       the *divergent* one.
///
///       So `stt_div a emp post` is inhabited for **every** post -- a computation that
///       never returns satisfies any partial-correctness specification. An axiom stated
///       there costs nothing because it says nothing: it would be discharged by a
///       program that hangs. `stt` admits no such realiser.
///
///       This is why "accept partial correctness for the object encoding" is not the
///       cheap option it appears to be. pal-csharp emits terminating `fn`s throughout --
///       F2 requires a `decreases` on every `while` precisely to stay out of `stt_div` --
///       so moving the object encoding to `stt_div` would give up termination for the
///       whole translation, not just for dispatch. Stating F30's axiom in `stt` keeps
///       that guarantee and confines the assumption to what it is really about: that
///       recovering an object from a reference terminates and yields the object stored.
///       A CLR cast does exactly that.

let rec loopd (#a: Type u#a) (#post: a -> slprop) (u: unit)
  : Dv (Pulse.Lib.Core.stt_div a emp post)
  = loopd #a #post ()

let diverge (#a: Type u#a) (#post: a -> slprop) : Pulse.Lib.Core.stt_div a emp post
  = Pulse.Lib.Core.hide_div (loopd #a #post)

let absurd_is_inhabited_in_stt_div
  : Pulse.Lib.Core.stt_div unit emp (fun _ -> pure False) = diverge

[@@expect_failure]
let absurd_is_inhabited_in_stt : stt unit emp (fun _ -> pure False) = diverge

/// F30c: `val stt (a:Type u#a) (pre:slprop) (post:a -> slprop) : Type0` -- a Pulse
///       computation type is `Type0` whatever universe its *result* lives in. So the
///       method fields of the vtable are not what raises its universe; the invariant
///       field, of type `impl -> perm -> shape__model -> slprop`, is. Any attempt to
///       shrink the vtable has to attack `inv`, not `area`.

let stt_is_type0_at_any_result_universe : Type0 =
  stt shape__obj emp (fun _ -> emp)


// ---------------------------------------------------------------------------------
// F31: a stored Pulse computation must be let-bound before it is applied.
// ---------------------------------------------------------------------------------

/// F31: Pulse runs an `stt`-valued term only when it appears as the head of the
///      application. Applying a *projection* -- `ob.pkg.area ob.rep` -- binds the
///      computation as a value instead of running it, and the `let` is then rejected
///      with the computation type in place of the result type. Let-binding the field
///      first (`let f = ob.pkg.area; let v = f ob.rep;`) makes it the head symbol and
///      the call goes through. Pulse.Lib.Par relies on the same property when it calls
///      a `unit -> stt _ _ _` parameter as `f ();`.
///
///      Every virtual call the emitter produces is a projection out of a vtable, so
///      this shape is forced on the rule, not a matter of taste.

[@@expect_failure]
fn dispatch_without_let_binding (s: shape) (#p: perm) (#m: erased shape__model)
  preserves shape__inv s #p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (shape__inv s #p m);
  with o. assert (shape__at o p m);
  let ob = undyn_stt #shape__obj #o s;
  rewrite (shape__at o p m) as (shape__at ob p m);
  unfold (shape__at ob p m);
  let v = ob.pkg.area ob.rep #p #m;
  fold (shape__at ob p m);
  rewrite (shape__at ob p m) as (shape__at o p m);
  fold (shape__inv s #p m);
  v
}

/// F31 (positive): the same body with the vtable slot let-bound first.

fn shape_area (s: shape) (#p: perm) (#m: erased shape__model)
  preserves shape__inv s #p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (shape__inv s #p m);
  with o. assert (shape__at o p m);
  let ob = undyn_stt #shape__obj #o s;
  rewrite (shape__at o p m) as (shape__at ob p m);
  unfold (shape__at ob p m);
  let f = ob.pkg.area;
  let v = f ob.rep #p #m;
  fold (shape__at ob p m);
  rewrite (shape__at ob p m) as (shape__at o p m);
  fold (shape__inv s #p m);
  v
}


// ---------------------------------------------------------------------------------
// F32: a subclass model may be larger than the base model.
// ---------------------------------------------------------------------------------

/// F32: the vtable fixes one `shape__model`, but `Circle` needs a radius that `Shape`
///      has no name for. The subclass keeps its own model and supplies a pure forgetful
///      map into the base one; the base invariant, as the subclass implements it, is
///      "there exists an extended model that forgets to `m`". This is exactly F17's
///      abstraction function one level up the hierarchy, and it means the *design* may
///      not fix a single model type for a hierarchy.

noeq type circle__model = { c_radius: int; c_area: int }
let circle__forget (m: circle__model) : shape__model = m.c_area

noeq type circle__raw = { fld_r: I32.t; fld_a: I32.t }
let circle : Type0 = B.box circle__raw

let circle__inv (c: circle) (#[T.exact (`1.0R)] p: perm) (m: circle__model) : slprop =
  exists* (r: circle__raw). B.pts_to c #p r **
    pure (I32.v r.fld_r == m.c_radius /\ I32.v r.fld_a == m.c_area)

let circle__as_shape (c: circle) (#[T.exact (`1.0R)] p: perm) (m: shape__model) : slprop =
  exists* (cm: circle__model). circle__inv c #p cm ** pure (circle__forget cm == m)

fn circle_area (c: circle) (#p: perm) (#m: erased shape__model)
  preserves circle__as_shape c #p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (circle__as_shape c #p m);
  with cm. assert (circle__inv c #p cm);
  unfold (circle__inv c #p cm);
  let v = B.op_Bang c;
  fold (circle__inv c #p cm);
  fold (circle__as_shape c #p m);
  v.fld_a
}

/// A second implementation whose representation is not even the same shape of record,
/// to check that nothing above quietly assumed a common layout.

let square : Type0 = B.box I32.t

let square__as_shape (s: square) (#[T.exact (`1.0R)] p: perm) (m: shape__model) : slprop =
  exists* (side: I32.t). B.pts_to s #p side **
    pure (I32.v side * I32.v side == m /\ FStar.Int.size (I32.v side * I32.v side) 32)

fn square_area (s: square) (#p: perm) (#m: erased shape__model)
  preserves square__as_shape s #p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (square__as_shape s #p m);
  with side. assert (B.pts_to s #p side);
  let x = B.op_Bang s;
  fold (square__as_shape s #p m);
  I32.mul x x
}


// ---------------------------------------------------------------------------------
// F33: packing a class into a vtable needs an eta-expansion.
// ---------------------------------------------------------------------------------

/// F33: F21 gives every class invariant a meta-argument-defaulted permission binder, so
///      that `class_C__inv x m` means `class_C__inv x #1.0R m` and the fractional work
///      stayed textually additive. That binder is *implicit*, so the invariant does not
///      have the vtable field's type, which takes the permission explicitly. Assigning
///      it directly is rejected; the pack site must eta-expand.
///
///      A rule that emits `inv = class_C__inv` would therefore not compile, and this is
///      invisible until the first class is packed.

[@@expect_failure]
let pack_circle_directly : t_shape =
  { impl = circle; inv = circle__as_shape; area = circle_area }

let t_circle : t_shape =
  { impl = circle; inv = (fun c p m -> circle__as_shape c #p m); area = circle_area }

let t_square : t_shape =
  { impl = square; inv = (fun s p m -> square__as_shape s #p m); area = square_area }


// ---------------------------------------------------------------------------------
// F34: upcast is a ghost operation, but its fold needs an explicit witness.
// ---------------------------------------------------------------------------------

/// F34: `Shape s = c;` for a `Circle c` moves no memory -- it is a pure re-reading of
///      the resource, so it is a `ghost fn` and free at runtime, which is what the C#
///      semantics require. But the closing `fold` has to introduce the existential over
///      `shape__obj`, and Pulse solves existentials by matching: it cannot invert the
///      projections in `o.pkg.inv o.rep p m` to discover `o`. Naming that body as a
///      separate abbreviation (`shape__at`, above) gives the fold a head symbol whose
///      argument *is* the witness, and the match succeeds.
///
///      This is the same forced detail as R3.10d's `assert`-before-`fold`: an existential
///      that the prover cannot reach by matching must be spelled out.

ghost fn upcast_circle (c: circle) (#p: perm) (#m: erased shape__model)
  requires circle__as_shape c #p m
  ensures  shape__inv (Dn.mkdyn ({ pkg = t_circle; rep = c } <: shape__obj)) #p m
{
  rewrite (circle__as_shape c #p m)
       as (shape__at ({ pkg = t_circle; rep = c } <: shape__obj) p m);
  fold (shape__inv (Dn.mkdyn ({ pkg = t_circle; rep = c } <: shape__obj)) #p m);
}

ghost fn upcast_square (s: square) (#p: perm) (#m: erased shape__model)
  requires square__as_shape s #p m
  ensures  shape__inv (Dn.mkdyn ({ pkg = t_square; rep = s } <: shape__obj)) #p m
{
  rewrite (square__as_shape s #p m)
       as (shape__at ({ pkg = t_square; rep = s } <: shape__obj) p m);
  fold (shape__inv (Dn.mkdyn ({ pkg = t_square; rep = s } <: shape__obj)) #p m);
}

/// The payoff: one client, two implementations with different representations and
/// different model types, dispatched dynamically through the vtable.

fn client (c: circle) (s: square) (#mc #ms: erased shape__model)
  requires circle__as_shape c #1.0R mc ** square__as_shape s #1.0R ms
  returns v: I32.t
  ensures pure (I32.v v == reveal mc \/ I32.v v == reveal ms)
{
  upcast_circle c;
  upcast_square s;
  let a = shape_area (Dn.mkdyn ({ pkg = t_circle; rep = c } <: shape__obj)) #1.0R #mc;
  let b = shape_area (Dn.mkdyn ({ pkg = t_square; rep = s } <: shape__obj)) #1.0R #ms;
  drop_ (shape__inv (Dn.mkdyn ({ pkg = t_circle; rep = c } <: shape__obj)) #1.0R mc);
  drop_ (shape__inv (Dn.mkdyn ({ pkg = t_square; rep = s } <: shape__obj)) #1.0R ms);
  a
}
