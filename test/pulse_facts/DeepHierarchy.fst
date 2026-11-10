module DeepHierarchy

/// A worked design study: a **three-level** hierarchy in Pulse.
///
///     Shape
///      +-- Circle
///      +-- Quadrilateral            (abstract, with methods of its own)
///           +-- Square
///           +-- Rectangle
///
/// `ShapeHierarchy.fst` settled the two-level case. This file settles the question
/// that only appears at depth three: an **intermediate class is both a subclass and a
/// superclass**, so it must be packageable into its parent's vtable *and* be a vtable
/// of its own that further subclasses instantiate.
///
/// The finding that drives the whole file is in section 5. A reference is a
/// `FStar.Dyn.dyn`, and a dyn is made at exactly one witness type; there is no way to
/// view a value made at `quad__obj` as one made at `shape__obj`, because that is
/// injectivity of `mkdyn` again. So **the dyn is always made at the root's object
/// record**, and an intermediate class is reached through an *extension point* in the
/// root vtable -- one `Dn.dyn` field, `sub`, which the root declares without knowing
/// what any descendant will put in it.
///
/// What it demonstrates beyond the two-level study:
///
///   * an abstract intermediate class with its own model, its own virtual method
///     (`Perimeter`), and a *non-virtual* method of its own (`SemiPerimeter`) whose
///     body calls a virtual one;
///   * two subclasses of the intermediate class with different representations and
///     different model types, each forgetting through *two* levels;
///   * a sibling (`Circle`) that derives from the root directly and fills the
///     extension point with nothing;
///   * upcast at every edge of the hierarchy, all free at runtime;
///   * a heterogeneous `Shape[]` mixing all three concrete classes, and a
///     quadrilateral-only computation over the ones that are quadrilaterals.

open Pulse
open Pulse.Lib.ForEvery
open Pulse.Lib.ForEvery.Range

module A = Pulse.Lib.CSharp.Array
module B = Pulse.Lib.Box
module CA = Pulse.Lib.CSharp.Array
module Dn = FStar.Dyn
module I32 = FStar.Int32
module Seq = FStar.Seq
module T = FStar.Tactics
module R = Pulse.Lib.Reference
module Tr = Pulse.Lib.Trade

#lang-pulse

/// Machine-integer representability, spelled once.
let ok32 (x: int) : prop = FStar.Int.size x 32

let max32 : int = 2147483647


// =================================================================================
// 1. The base class `Shape`
// =================================================================================

/// ```csharp
/// [Model] public abstract class ShapeModel { public int Area; }
/// ```
/// The model shared by the whole hierarchy: a shape is known by its area. Every
/// subclass may model *more* than this (see `circle__model`), but this is what a
/// client holding a `Shape` gets to talk about.
let shape__model = int

/// The vtable. `impl` is the subclass's representation type, `inv` is its object
/// invariant read at the *base* model, and there is one field per virtual method.
///
/// F30c: `stt _ pre post : Type0` whatever universe its result lives in, so the two
/// method fields are harmless. It is `inv`, whose result is `slprop : Type u#4`, that
/// puts this record far above `Type0`.
noeq type t_shape = {
  impl : Type0;

  inv  : impl -> perm -> shape__model -> slprop;

  /// ```csharp
  /// [Ensures("Result == @this.Area")] public abstract int Area();
  /// ```
  /// Read-only, so it is generalised over the permission (F26): a `Shape` held at
  /// any fraction may be measured.
  area : (x:impl -> #p:perm -> #m:erased shape__model ->
          stt I32.t (inv x p m)
                    (fun v -> inv x p m ** pure (I32.v v == reveal m)));

  /// ```csharp
  /// [Requires("Ok32(4 * @this.Area)")]
  /// [Ensures("@this.Area == 4 * Old(@this.Area)")]
  /// public abstract void Double();
  /// ```
  /// Doubles every linear dimension, so the area quadruples. Mutating, so it demands
  /// the full permission and moves the model.
  dbl  : (x:impl -> #m:erased shape__model ->
          stt unit (inv x 1.0R m ** pure (ok32 (4 * reveal m)))
                   (fun _ -> inv x 1.0R (4 * reveal m)));

  /// R3.10c/d one level up: splitting and rejoining the permission. These are not
  /// derivable from `inv` -- how a permission distributes over an object's parts is
  /// the *implementation's* business -- so a hierarchy that supports read-only
  /// aliasing must carry them in the vtable.
  ///
  /// They are `stt_ghost`, which is the whole point: sharing a `Shape` is free at
  /// runtime even though the vtable is only reachable through a real computation.
  /// Ghost code may project a ghost package and run a ghost method out of it.
  share : (x:impl -> #p:perm -> #m:erased shape__model ->
           stt_ghost unit emp_inames
             (inv x p m)
             (fun _ -> inv x (p /. 2.0R) m ** inv x (p /. 2.0R) m));

  gather: (x:impl -> p:perm -> q:perm -> #m:erased shape__model -> #m2:erased shape__model ->
           stt_ghost unit emp_inames
             (inv x p m ** inv x q m2)
             (fun _ -> inv x (p +. q) m ** pure (reveal m == reveal m2)));

}

/// A fully applied object: a vtable together with a value of *its* implementation
/// type. This dependent pair is what a variable of static type `Shape` denotes -- and
/// by F28 it is far too big to live in a heap cell or an array.
noeq type shape__obj = {
  pkg: t_shape;
  rep: pkg.impl;

  /// THE EXTENSION POINT, and the one field the two-level study does not have.
  ///
  /// A class between `Shape` and a leaf adds virtual methods `Shape` has never heard
  /// of, and a `Shape`-typed reference must still reach them, because in this encoding
  /// the reference *is* the object -- see the note above `quad__inv` in section 5.
  /// `Shape` therefore declares one field of the erased type `Dn.dyn` and says nothing
  /// whatever about its contents; an intermediate class stores its own object record
  /// there, and its own invariant says what is in it.
  ///
  /// This is open-world, which is the point: `Shape` is compiled once and admits
  /// subclasses that do not exist yet. A sum type over the known subclasses -- the
  /// obvious cheaper encoding -- would not.
  ///
  /// It hangs off the *object* rather than the vtable because what a descendant needs
  /// to recover is a vtable *applied to a representation*; recovering a bare vtable
  /// would leave its `impl` type only propositionally equal to `pkg.impl`, and every
  /// use would need a coercion. Nothing is stored twice at runtime: `sub` and the
  /// object are the same reference, and a `recover` is a checked cast.
  sub: Dn.dyn;
}

/// F29: so a `Shape` *variable* is the promotion of that pair into `FStar.Dyn.dyn`,
/// which is `Type0` and therefore boxable, array-able, and admissible as a field.
let shape : Type0 = Dn.dyn

/// Named apart from `shape__inv` so that a `fold` can be handed an explicit witness
/// for the existential -- see F34.
let shape__at (o: shape__obj) (p: perm) (m: shape__model) : slprop = o.pkg.inv o.rep p m

/// The base-class object invariant. F21's meta-argument default keeps `shape__inv s m`
/// meaning `shape__inv s #1.0R m`.
let shape__inv (s: shape) (#[T.exact (`1.0R)] p: perm) (m: shape__model) : slprop =
  exists* (o: shape__obj). pure (s == Dn.mkdyn o) ** shape__at o p m

/// THE ONE AXIOM (F30). A CLR reference denotes the object it was made from: an upcast
/// changes only the static type, and recovering the object yields the one that was
/// stored. `FStar.Dyn.undyn` models the recovery but ships in `Dv` with no equation
/// relating its result to its argument, and no such equation is provable, since `Dv`
/// results cannot be equated in specifications.
///
/// Stated in `stt` rather than `stt_div` deliberately (F30b): in `stt_div` every
/// postcondition is inhabited by a computation that hangs, so the axiom would say
/// nothing. Here it says exactly one thing beyond what F* can prove -- that the
/// recovery terminates and is faithful -- which is what the CLR object header is for.
assume
val recover (#a: Type u#a) (#x: erased a) (d: Dn.dyn { d == Dn.mkdyn (reveal x) })
  : stt a emp (fun y -> pure (y == reveal x))


// =================================================================================
// 2. Virtual dispatch
// =================================================================================

/// ```csharp
/// int a = s.Area();     // s : Shape
/// ```
/// F31: the vtable slot must be let-bound before it is applied. `ob.pkg.area ob.rep`
/// binds the computation instead of running it.
fn shape_area (s: shape) (#p: perm) (#m: erased shape__model)
  preserves shape__inv s #p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (shape__inv s #p m);
  with o. assert (shape__at o p m);
  let ob = recover #shape__obj #o s;
  rewrite (shape__at o p m) as (shape__at ob p m);
  unfold (shape__at ob p m);
  let f = ob.pkg.area;
  let v = f ob.rep #p #m;
  fold (shape__at ob p m);
  rewrite (shape__at ob p m) as (shape__at o p m);
  fold (shape__inv s #p m);
  v
}

/// ```csharp
/// s.Double();           // s : Shape
/// ```
/// The mutating case: full permission in, and the model moves.
fn shape_double (s: shape) (#m: erased shape__model)
  requires shape__inv s #1.0R m ** pure (ok32 (4 * reveal m))
  ensures  shape__inv s #1.0R (4 * reveal m)
{
  unfold (shape__inv s #1.0R m);
  with o. assert (shape__at o 1.0R m);
  let ob = recover #shape__obj #o s;
  rewrite (shape__at o 1.0R m) as (shape__at ob 1.0R m);
  unfold (shape__at ob 1.0R m);
  let f = ob.pkg.dbl;
  f ob.rep #m;
  fold (shape__at ob 1.0R (4 * reveal m));
  rewrite (shape__at ob 1.0R (4 * reveal m)) as (shape__at o 1.0R (4 * reveal m));
  fold (shape__inv s #1.0R (4 * reveal m));
}

/// ```csharp
/// Pal.Share(s);         // s : Shape
/// ```
/// The payoff of putting `share`/`gather` in the vtable as `stt_ghost`: dispatched
/// sharing is a **ghost** operation, so read-only aliasing of a `Shape` costs nothing
/// at runtime -- even though the vtable is otherwise reachable only through `recover`,
/// which is a real computation.
///
/// It works because ghost code never needs the vtable as a *value*: the package is
/// already available as the ghost witness of `shape__inv`'s existential, and projecting
/// a ghost record and running a ghost method out of it is erasable.
ghost fn shape_share (s: shape) (#p: perm) (#m: erased shape__model)
  requires shape__inv s #p m
  ensures  shape__inv s #(p /. 2.0R) m ** shape__inv s #(p /. 2.0R) m
{
  unfold (shape__inv s #p m);
  with o. assert (shape__at o p m);
  unfold (shape__at o p m);
  let f = o.pkg.share;
  f o.rep #p #m;
  fold (shape__at o (p /. 2.0R) m);
  fold (shape__at o (p /. 2.0R) m);
  fold (shape__inv s #(p /. 2.0R) m);
  fold (shape__inv s #(p /. 2.0R) m);
}

/// ...but `gather` does **not** dispatch, and the reason is the sharpest constraint in
/// the whole encoding.
///
/// Two views of the same `Shape` unfold to two *separate* existential witnesses `o1`
/// and `o2`, with only `s == mkdyn o1` and `s == mkdyn o2` to relate them. Concluding
/// `o1 == o2` is exactly injectivity of `mkdyn` -- and injectivity cannot be assumed:
/// `mkdyn` is universe polymorphic into `Type0`, so an injection would embed arbitrarily
/// large types into a small one and Cantor's argument applies. `FStar.Dyn` omits
/// injectivity deliberately, not by oversight.
///
/// Separation logic cannot supply the missing step either: owning two fractions of two
/// objects is not evidence that they are one object.
[@@expect_failure; allow_ambiguous]
ghost fn shape_gather_unindexed (s: shape) (p q: perm)
                                (#m: erased shape__model) (#m2: erased shape__model)
  requires shape__inv s #p m ** shape__inv s #q m2
  ensures  shape__inv s #(p +. q) m ** pure (reveal m == reveal m2)
{
  unfold (shape__inv s #p m);
  with o. assert (shape__at o p m);
  unfold (shape__inv s #q m2);
  with o2. assert (shape__at o2 q m2);
  rewrite (shape__at o2 q m2) as (shape__at o q m2);
  admit()
}

/// The fix is not another axiom but an extra *ghost index*: state the invariant at a
/// named implementation package. Two views of one object are then two views at the
/// same `o` by construction, and gather goes through with nothing assumed.
///
/// This is the right answer on its own terms, too. A CLR object's dynamic type is
/// fixed for its lifetime, so making it ghost-visible states a true fact; and a client
/// that wants to forget which implementation it holds can existentially quantify `o`
/// itself, which is precisely `shape__inv`.
let shape__inv_at (s: shape) (o: erased shape__obj) (p: perm) (m: shape__model) : slprop =
  pure (s == Dn.mkdyn (reveal o)) ** shape__at o p m

/// Forgetting the index recovers the plain invariant; the reverse direction is a
/// `with`-binding at the use site, since only the prover can name the witness.
ghost fn shape_forget_impl (s: shape) (o: erased shape__obj) (#p: perm) (#m: erased shape__model)
  requires shape__inv_at s o p m
  ensures  shape__inv s #p m
{
  unfold (shape__inv_at s o p m);
  fold (shape__inv s #p m);
}

ghost fn shape_share_at (s: shape) (o: erased shape__obj) (#p: perm) (#m: erased shape__model)
  requires shape__inv_at s o p m
  ensures  shape__inv_at s o (p /. 2.0R) m ** shape__inv_at s o (p /. 2.0R) m
{
  unfold (shape__inv_at s o p m);
  unfold (shape__at o p m);
  let f = o.pkg.share;
  f o.rep #p #m;
  fold (shape__at o (p /. 2.0R) m);
  fold (shape__at o (p /. 2.0R) m);
  fold (shape__inv_at s o (p /. 2.0R) m);
  fold (shape__inv_at s o (p /. 2.0R) m);
}

[@@allow_ambiguous]
ghost fn shape_gather_at (s: shape) (o: erased shape__obj) (p q: perm)
                         (#m: erased shape__model) (#m2: erased shape__model)
  requires shape__inv_at s o p m ** shape__inv_at s o q m2
  ensures  shape__inv_at s o (p +. q) m ** pure (reveal m == reveal m2)
{
  unfold (shape__inv_at s o p m);
  unfold (shape__inv_at s o q m2);
  unfold (shape__at o p m);
  unfold (shape__at o q m2);
  let g = o.pkg.gather;
  g o.rep p q #m #m2;
  fold (shape__at o (p +. q) m);
  fold (shape__inv_at s o (p +. q) m);
}


/// A method at the indexed invariant. Every real method should be stated this way and
/// the un-indexed form derived, because a client that goes through the un-indexed form
/// *loses* the index and can never gather again.
fn shape_area_at (s: shape) (#o: erased shape__obj) (#p: perm) (#m: erased shape__model)
  preserves shape__inv_at s o p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (shape__inv_at s o p m);
  let ob = recover #shape__obj #o s;
  rewrite (shape__at o p m) as (shape__at ob p m);
  unfold (shape__at ob p m);
  let f = ob.pkg.area;
  let v = f ob.rep #p #m;
  fold (shape__at ob p m);
  rewrite (shape__at ob p m) as (shape__at o p m);
  fold (shape__inv_at s o p m);
  v
}

// =================================================================================
// 3. Arithmetic side conditions
// =================================================================================

/// Doubling a linear dimension cannot overflow if the *quadrupled area* does not.
/// Both subclasses need this and neither can get it from Z3 unaided: it is the one
/// genuinely nonlinear step in the development.
let double_fits (c: pos) (d: int)
  : Lemma (requires 0 <= d /\ ok32 (4 * (c * d * d)))
          (ensures  ok32 (2 * d))
  = if d >= 1 then begin
      FStar.Math.Lemmas.lemma_mult_le_right d 2 (4 * c * d);
      assert (2 * d <= 4 * c * d * d)
    end


// =================================================================================
// 4. Subclass `Circle`
// =================================================================================

/// ```csharp
/// public sealed class Circle : Shape {
///     private int radius;
///     ...
/// }
/// ```
/// F32: `Circle`'s model is *larger* than `Shape`'s -- it has a radius, which `Shape`
/// has no name for. The subclass keeps its own model type and supplies a pure
/// forgetful map into the base one. A hierarchy therefore may not fix a single model.
noeq type circle__model = { c_radius: int }

/// Area of a circle, in this development's arithmetic: 3r^2.
let circle__forget (cm: circle__model) : shape__model = 3 * cm.c_radius * cm.c_radius

noeq type circle__raw = { fld_radius: I32.t }
let circle : Type0 = B.box circle__raw

/// The concrete invariant R4.10 unfolds inside `Circle`'s own methods.
let circle__inv (c: circle) (#[T.exact (`1.0R)] p: perm) (cm: circle__model) : slprop =
  exists* (r: circle__raw).
    B.pts_to c #p r **
    pure (I32.v r.fld_radius == cm.c_radius /\ 0 <= cm.c_radius)

/// The base invariant, as `Circle` implements it: a Circle at base model `m` is a
/// Circle at *some* extended model that forgets to `m`. This is F17's abstraction
/// function one level up the hierarchy.
let circle__as_shape (c: circle) (#[T.exact (`1.0R)] p: perm) (m: shape__model) : slprop =
  exists* (cm: circle__model).
    circle__inv c #p cm ** pure (circle__forget cm == m /\ ok32 m)

fn circle_area (c: circle) (#p: perm) (#m: erased shape__model)
  preserves circle__as_shape c #p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (circle__as_shape c #p m);
  with cm. assert (circle__inv c #p cm);
  unfold (circle__inv c #p cm);
  let r = B.op_Bang c;
  let rr = I32.mul r.fld_radius r.fld_radius;
  let a = I32.mul rr 3l;
  fold (circle__inv c #p cm);
  fold (circle__as_shape c #p m);
  a
}

fn circle_double (c: circle) (#m: erased shape__model)
  requires circle__as_shape c #1.0R m ** pure (ok32 (4 * reveal m))
  ensures  circle__as_shape c #1.0R (4 * reveal m)
{
  unfold (circle__as_shape c #1.0R m);
  with cm. assert (circle__inv c #1.0R cm);
  unfold (circle__inv c #1.0R cm);
  double_fits 3 cm.c_radius;
  let r = B.op_Bang c;
  let r2 = I32.mul r.fld_radius 2l;
  B.op_Colon_Equals c { fld_radius = r2 };
  fold (circle__inv c #1.0R ({ c_radius = 2 * cm.c_radius }));
  fold (circle__as_shape c #1.0R (4 * reveal m));
}

ghost fn circle_share (c: circle) (#p: perm) (#m: erased shape__model)
  requires circle__as_shape c #p m
  ensures  circle__as_shape c #(p /. 2.0R) m ** circle__as_shape c #(p /. 2.0R) m
{
  unfold (circle__as_shape c #p m);
  with cm. assert (circle__inv c #p cm);
  unfold (circle__inv c #p cm);
  with r. assert (B.pts_to c #p r);
  B.share c;
  assert (B.pts_to c #(p /. 2.0R) r ** B.pts_to c #(p /. 2.0R) r);
  fold (circle__inv c #(p /. 2.0R) cm);
  fold (circle__inv c #(p /. 2.0R) cm);
  fold (circle__as_shape c #(p /. 2.0R) m);
  fold (circle__as_shape c #(p /. 2.0R) m);
}

[@@allow_ambiguous]
ghost fn circle_gather (c: circle) (p q: perm)
                       (#m: erased shape__model) (#m2: erased shape__model)
  requires circle__as_shape c #p m ** circle__as_shape c #q m2
  ensures  circle__as_shape c #(p +. q) m ** pure (reveal m == reveal m2)
{
  unfold (circle__as_shape c #p m);
  with cm. assert (circle__inv c #p cm);
  unfold (circle__inv c #p cm);
  with r. assert (B.pts_to c #p r);

  unfold (circle__as_shape c #q m2);
  with cm2. assert (circle__inv c #q cm2);
  unfold (circle__inv c #q cm2);
  with r2. assert (B.pts_to c #q r2);

  B.pts_to_injective_eq c;
  rewrite (B.pts_to c #q r2) as (B.pts_to c #q r);
  B.gather c;
  assert (pure (cm == cm2));
  fold (circle__inv c #(p +. q) cm);
  fold (circle__as_shape c #(p +. q) m);
}

/// F33: `inv = circle__as_shape` does not typecheck -- F21's permission binder is
/// implicit, and the vtable field takes it explicitly. The pack site must eta-expand.
let t_circle : t_shape = {
  impl = circle;
  inv  = (fun c p m -> circle__as_shape c #p m);
  area = circle_area;
  dbl  = circle_double;
  share = circle_share;
  gather = circle_gather;
}

/// ```csharp
/// Shape s = c;          // c : Circle
/// ```
/// F34: an upcast moves no memory, so it is a `ghost fn` and free at runtime -- which
/// is what the C# semantics require. The closing `fold` needs `shape__at` to give the
/// existential a head symbol whose argument is the witness.
ghost fn upcast_circle (c: circle) (#p: perm) (#m: erased shape__model)
  requires circle__as_shape c #p m
  ensures  shape__inv (Dn.mkdyn ({ pkg = t_circle; rep = c; sub = Dn.mkdyn () } <: shape__obj)) #p m
{
  rewrite (circle__as_shape c #p m)
       as (shape__at ({ pkg = t_circle; rep = c; sub = Dn.mkdyn () } <: shape__obj) p m);
  fold (shape__inv (Dn.mkdyn ({ pkg = t_circle; rep = c; sub = Dn.mkdyn () } <: shape__obj)) #p m);
}

/// ```csharp
/// Shape s = new Circle(r);
/// ```
/// A constructor is *static*: it is not dispatched on a value you already hold, so it
/// does not belong in the vtable. It allocates, establishes the concrete invariant,
/// re-reads it at the base model, and upcasts.
fn new_circle (r: I32.t)
  requires pure (0 <= I32.v r /\ ok32 (3 * I32.v r * I32.v r))
  returns  s: shape
  ensures  shape__inv s #1.0R (3 * I32.v r * I32.v r)
{
  let c = B.alloc ({ fld_radius = r });
  fold (circle__inv c #1.0R ({ c_radius = I32.v r }));
  fold (circle__as_shape c #1.0R (3 * I32.v r * I32.v r));
  upcast_circle c;
  Dn.mkdyn ({ pkg = t_circle; rep = c; sub = Dn.mkdyn () } <: shape__obj)
}


// =================================================================================


// =================================================================================
// 5. The intermediate class `Quadrilateral`
// =================================================================================

/// ```csharp
/// [Model] public abstract class QuadModel : ShapeModel { public int W; public int H; }
/// ```
/// A quadrilateral is known by its bounding box, and its area is the product. As with
/// `circle__model`, this is *larger* than the base model, and forgets into it.
///
/// **Why a bounding box and not `{ Area, Perimeter }`**, which is the obvious choice.
/// `Shape.Double`'s precondition is `ok32 (4 * Area)`, and that is all a subclass gets
/// to assume. From it, `2*W` and `2*H` are representable whenever `W, H >= 1`, because
/// `2*W <= 4*W*H`; the same argument is the one `double_fits` makes for a radius or a
/// side. A *perimeter* admits no such argument: isoperimetry gives `P^2 >= 16*A` and no
/// upper bound at all, so a 1-by-n rectangle has perimeter about twice its area and
/// `ok32 (4 * Area)` does not imply `ok32 (2 * P)`.
///
/// That is not an artifact of this example. It says that **a virtual method's
/// precondition, written at the base model, must be strong enough for every subclass's
/// model** -- and where it is not, the base class must either state the precondition
/// abstractly (a vtable-supplied predicate over the representation) or expose a virtual
/// query for it. Choosing a model whose quantities are bounded by the base model's is
/// the cheap way out, and the one a C# surface should push users towards.
noeq type quad__model = { q_w: int; q_h: int }

let quad__forget (qm: quad__model) : shape__model = qm.q_w * qm.q_h

/// The vtable of the intermediate class. It lists **every method visible at this
/// level**, inherited ones included, each read at *this* level's model -- exactly as a
/// real vtable re-lists the slots it inherits. That is what lets a `Quadrilateral`-typed
/// reference call `Area()` and keep its bounding box, which a client that had upcast to
/// `Shape` and back could not.
noeq type t_quad = {
  qimpl : Type0;

  qinv  : qimpl -> perm -> quad__model -> slprop;

  /// Inherited from `Shape`, at the quadrilateral model.
  qarea : (x:qimpl -> #p:perm -> #qm:erased quad__model ->
           stt I32.t (qinv x p qm)
                     (fun v -> qinv x p qm ** pure (I32.v v == quad__forget qm)));

  qdbl  : (x:qimpl -> #qm:erased quad__model ->
           stt unit (qinv x 1.0R qm ** pure (ok32 (4 * quad__forget qm)))
                    (fun _ -> qinv x 1.0R ({ q_w = 2 * (reveal qm).q_w;
                                             q_h = 2 * (reveal qm).q_h })));

  /// ```csharp
  /// [Requires("Ok32(2 * (@this.W + @this.H))")]
  /// [Ensures("Result == 2 * (@this.W + @this.H)")]
  /// public abstract int Perimeter();
  /// ```
  /// `Quadrilateral`'s own virtual method. Note that it carries a precondition of its
  /// own, stated over the quadrilateral model -- which a caller holding a
  /// `Quadrilateral` can discharge, and a caller holding a `Shape` cannot even write.
  qperim: (x:qimpl -> #p:perm -> #qm:erased quad__model ->
           stt I32.t (qinv x p qm **
                      pure (ok32 (2 * ((reveal qm).q_w + (reveal qm).q_h))))
                     (fun v -> qinv x p qm **
                               pure (I32.v v == 2 * ((reveal qm).q_w + (reveal qm).q_h))));

  qshare : (x:qimpl -> #p:perm -> #qm:erased quad__model ->
            stt_ghost unit emp_inames
              (qinv x p qm)
              (fun _ -> qinv x (p /. 2.0R) qm ** qinv x (p /. 2.0R) qm));

  qgather: (x:qimpl -> p:perm -> q:perm ->
            #qm:erased quad__model -> #qm2:erased quad__model ->
            stt_ghost unit emp_inames
              (qinv x p qm ** qinv x q qm2)
              (fun _ -> qinv x (p +. q) qm ** pure (reveal qm == reveal qm2)));
}

/// The intermediate class's own applied object, exactly as `shape__obj` is the root's.
noeq type quad__obj = { qpkg: t_quad; qrep: qpkg.qimpl }

let quad__at (qo: quad__obj) (p: perm) (qm: quad__model) : slprop =
  qo.qpkg.qinv qo.qrep p qm

/// The `Shape` face of a quadrilateral vtable: forget the bounding box and keep the
/// area. This is the same abstraction-function step a leaf class makes (`circle__inv`
/// to `circle__as_shape`) -- an intermediate class is just a class, and makes it too.
let quad__as_shape (qp: t_quad) (x: qp.qimpl) (p: perm) (m: shape__model) : slprop =
  exists* (qm: quad__model). qp.qinv x p qm ** pure (quad__forget qm == m)

/// The four inherited methods, derived **once and for all** from any `t_quad`. This is
/// what makes the encoding pay off: `Square` and `Rectangle` below implement the
/// quadrilateral vtable only, and get their `Shape` vtable for free. Each wrapper does
/// nothing but re-read the model at the coarser level.
fn quad_pkg_area (qp: t_quad) (x: qp.qimpl) (#p: perm) (#m: erased shape__model)
  preserves quad__as_shape qp x p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (quad__as_shape qp x p m);
  with qm. assert (qp.qinv x p qm);
  let f = qp.qarea;
  let v = f x #p #qm;
  fold (quad__as_shape qp x p m);
  v
}

fn quad_pkg_dbl (qp: t_quad) (x: qp.qimpl) (#m: erased shape__model)
  requires quad__as_shape qp x 1.0R m ** pure (ok32 (4 * reveal m))
  ensures  quad__as_shape qp x 1.0R (4 * reveal m)
{
  unfold (quad__as_shape qp x 1.0R m);
  with qm. assert (qp.qinv x 1.0R qm);
  let f = qp.qdbl;
  f x #qm;
  fold (quad__as_shape qp x 1.0R (4 * reveal m));
}

ghost fn quad_pkg_share (qp: t_quad) (x: qp.qimpl) (#p: perm) (#m: erased shape__model)
  requires quad__as_shape qp x p m
  ensures  quad__as_shape qp x (p /. 2.0R) m ** quad__as_shape qp x (p /. 2.0R) m
{
  unfold (quad__as_shape qp x p m);
  with qm. assert (qp.qinv x p qm);
  let f = qp.qshare;
  f x #p #qm;
  fold (quad__as_shape qp x (p /. 2.0R) m);
  fold (quad__as_shape qp x (p /. 2.0R) m);
}

[@@allow_ambiguous]
ghost fn quad_pkg_gather (qp: t_quad) (x: qp.qimpl) (p: perm) (q: perm)
                         (#m: erased shape__model) (#m2: erased shape__model)
  requires quad__as_shape qp x p m ** quad__as_shape qp x q m2
  ensures  quad__as_shape qp x (p +. q) m ** pure (reveal m == reveal m2)
{
  unfold (quad__as_shape qp x p m);
  with qm. assert (qp.qinv x p qm);
  unfold (quad__as_shape qp x q m2);
  with qm2. assert (qp.qinv x q qm2);
  let f = qp.qgather;
  f x p q #qm #qm2;
  fold (quad__as_shape qp x (p +. q) m);
}

/// ```csharp
/// // the compiler-generated Shape vtable for any class deriving from Quadrilateral
/// ```
/// F33's eta-expansion again, at every slot.
let quad_as_shape_pkg (qp: t_quad) : t_shape = {
  impl   = qp.qimpl;
  inv    = (fun x p m -> quad__as_shape qp x p m);
  area   = (fun x #p #m -> quad_pkg_area qp x #p #m);
  dbl    = (fun x #m -> quad_pkg_dbl qp x #m);
  share  = (fun x #p #m -> quad_pkg_share qp x #p #m);
  gather = (fun x p q #m #m2 -> quad_pkg_gather qp x p q #m #m2);
}


// =================================================================================
// 6. What a `Quadrilateral`-typed reference is, and how it dispatches
// =================================================================================

/// **The finding this file exists for.**
///
/// A reference is a `Dn.dyn`, and a dyn is made at exactly one witness type. There is
/// no way to view a value made at `quad__obj` as one made at `shape__obj`: that is
/// injectivity of `mkdyn`, which section 3 of `ShapeHierarchy.fst` shows cannot be
/// assumed. So an upcast cannot rebuild the dyn, and a `Quadrilateral` variable cannot
/// be a dyn of a `quad__obj`.
///
/// Therefore **the dyn is always made at the root's object record**, and an
/// intermediate class is a *view* of it: `shape_view` says what root object a
/// quadrilateral presents itself as, and `sub` carries the quadrilateral object back.
/// Both directions are pure functions, so every cast in the hierarchy is free.
///
/// Note that `quad` and `shape` are the *same* C# reference and the same F\* value; only
/// the invariant differs. That is exactly the C# semantics of a reference conversion.
let shape_view (qo: quad__obj) : shape__obj =
  { pkg = quad_as_shape_pkg qo.qpkg; rep = qo.qrep; sub = Dn.mkdyn qo }

/// The intermediate class's object invariant, over a reference of the *same* type as a
/// `Shape`. A `Quadrilateral` is a `Shape` whose root object happens to be the view of
/// some quadrilateral object -- and it is the invariant, not the value, that records it.
let quad__inv (s: shape) (#[T.exact (`1.0R)] p: perm) (qm: quad__model) : slprop =
  exists* (qo: quad__obj). pure (s == Dn.mkdyn (shape_view qo)) ** quad__at qo p qm

/// The same invariant with the implementation package **named**, as `shape__inv_at`
/// names it in the two-level study. There it was forced by `gather`; here it turns out
/// to be the same thing a caller needs to perform a **checked downcast** (section 14),
/// which is a pleasing coincidence and not really a coincidence at all: both ask the
/// client to know *which* implementation it is holding, and both are satisfied by
/// remembering rather than by testing.
let quad__inv_at (s: shape) (qo: erased quad__obj) (p: perm) (qm: quad__model) : slprop =
  pure (s == Dn.mkdyn (shape_view (reveal qo))) ** quad__at qo p qm

ghost fn quad_forget_impl (s: shape) (qo: erased quad__obj)
                          (#p: perm) (#qm: erased quad__model)
  requires quad__inv_at s qo p qm
  ensures  quad__inv s #p qm
{
  unfold (quad__inv_at s qo p qm);
  fold (quad__inv s #p qm);
}

/// ```csharp
/// Shape s = q;          // q : Quadrilateral
/// ```
/// The upcast across the *inner* edge of the hierarchy. Ghost, so free -- and, unlike
/// the leaf upcasts, it needs no knowledge of the concrete class at all.
ghost fn upcast_quad (s: shape) (#p: perm) (#qm: erased quad__model)
  requires quad__inv s #p qm
  ensures  shape__inv s #p (quad__forget qm)
{
  unfold (quad__inv s #p qm);
  with qo. assert (quad__at qo p qm);
  unfold (quad__at qo p qm);
  fold (quad__as_shape qo.qpkg qo.qrep p (quad__forget qm));
  rewrite (quad__as_shape qo.qpkg qo.qrep p (quad__forget qm))
       as (shape__at (shape_view qo) p (quad__forget qm));
  fold (shape__inv s #p (quad__forget qm));
}

/// ```csharp
/// int p = q.Perimeter();    // q : Quadrilateral
/// ```
/// Dispatch at the intermediate level costs **two** recoveries: one to reach the root
/// object, one to follow `sub` to the quadrilateral object. In extracted terms both are
/// casts on the same reference. F31's let-binding rule applies to the inner slot just
/// as it does to the outer one.
fn quad_perimeter_at (s: shape) (#qo: erased quad__obj) (#p: perm)
                     (#qm: erased quad__model)
  requires quad__inv_at s qo p qm **
           pure (ok32 (2 * ((reveal qm).q_w + (reveal qm).q_h)))
  returns  v: I32.t
  ensures  quad__inv_at s qo p qm **
           pure (I32.v v == 2 * ((reveal qm).q_w + (reveal qm).q_h))
{
  unfold (quad__inv_at s qo p qm);
  let ob = recover #shape__obj #(hide (shape_view (reveal qo))) s;
  assert (pure (ob.sub == Dn.mkdyn (reveal qo)));
  let qob = recover #quad__obj #qo ob.sub;
  rewrite (quad__at qo p qm) as (quad__at qob p qm);
  unfold (quad__at qob p qm);
  let f = qob.qpkg.qperim;
  let v = f qob.qrep #p #qm;
  fold (quad__at qob p qm);
  rewrite (quad__at qob p qm) as (quad__at qo p qm);
  fold (quad__inv_at s qo p qm);
  v
}

/// The unindexed method is the indexed one composed with forgetting -- which is the
/// general recipe, and the reason indexing costs nothing in expressiveness: a client
/// that never downcasts simply forgets at every call, and a client that will downcast
/// keeps the index and calls the primitive. Only the primitive dispatches.
fn quad_perimeter (s: shape) (#p: perm) (#qm: erased quad__model)
  requires quad__inv s #p qm **
           pure (ok32 (2 * ((reveal qm).q_w + (reveal qm).q_h)))
  returns  v: I32.t
  ensures  quad__inv s #p qm **
           pure (I32.v v == 2 * ((reveal qm).q_w + (reveal qm).q_h))
{
  unfold (quad__inv s #p qm);
  with qo. assert (quad__at qo p qm);
  fold (quad__inv_at s (hide qo) p qm);
  let v = quad_perimeter_at s #(hide qo) #p #qm;
  quad_forget_impl s (hide qo);
  v
}

/// ```csharp
/// int a = q.Area();         // q : Quadrilateral
/// ```
/// An *inherited* method, called at the intermediate static type. It dispatches through
/// the quadrilateral vtable rather than the root one, which is why the bounding box
/// survives the call: a client that upcast to `Shape` and called `Area()` there would
/// keep only the area.
fn quad_area_at (s: shape) (#qo: erased quad__obj) (#p: perm)
                (#qm: erased quad__model)
  preserves quad__inv_at s qo p qm
  returns  v: I32.t
  ensures  pure (I32.v v == quad__forget qm)
{
  unfold (quad__inv_at s qo p qm);
  let ob = recover #shape__obj #(hide (shape_view (reveal qo))) s;
  let qob = recover #quad__obj #qo ob.sub;
  rewrite (quad__at qo p qm) as (quad__at qob p qm);
  unfold (quad__at qob p qm);
  let f = qob.qpkg.qarea;
  let v = f qob.qrep #p #qm;
  fold (quad__at qob p qm);
  rewrite (quad__at qob p qm) as (quad__at qo p qm);
  fold (quad__inv_at s qo p qm);
  v
}

fn quad_area (s: shape) (#p: perm) (#qm: erased quad__model)
  preserves quad__inv s #p qm
  returns  v: I32.t
  ensures  pure (I32.v v == quad__forget qm)
{
  unfold (quad__inv s #p qm);
  with qo. assert (quad__at qo p qm);
  fold (quad__inv_at s (hide qo) p qm);
  let v = quad_area_at s #(hide qo) #p #qm;
  quad_forget_impl s (hide qo);
  v
}

/// ```csharp
/// q.Double();               // q : Quadrilateral
/// ```
fn quad_double (s: shape) (#qm: erased quad__model)
  requires quad__inv s #1.0R qm ** pure (ok32 (4 * quad__forget qm))
  ensures  quad__inv s #1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h })
{
  unfold (quad__inv s #1.0R qm);
  with qo. assert (quad__at qo 1.0R qm);
  let ob = recover #shape__obj #(hide (shape_view qo)) s;
  let qob = recover #quad__obj #qo ob.sub;
  rewrite (quad__at qo 1.0R qm) as (quad__at qob 1.0R qm);
  unfold (quad__at qob 1.0R qm);
  let f = qob.qpkg.qdbl;
  f qob.qrep #qm;
  fold (quad__at qob 1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h }));
  rewrite (quad__at qob 1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h }))
       as (quad__at qo 1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h }));
  fold (quad__inv s #1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h }));
}

/// ```csharp
/// public int SemiPerimeter() { return Perimeter() / 2; }   // in Quadrilateral
/// ```
/// A **non-virtual method of the intermediate class**, whose body calls one of its own
/// virtual methods. It is an ordinary `fn` over `quad__inv`: there is no vtable slot for
/// it, no recovery of its own, and it works for every present and future subclass.
///
/// This is also the first time in either study that a method calls a virtual method on
/// its own receiver, and it needs nothing special -- the invariant is folded on the way
/// in, which is precisely what `quad_perimeter` asks for (R4.10).
fn quad_semi_perimeter (s: shape) (#p: perm) (#qm: erased quad__model)
  requires quad__inv s #p qm **
           pure (ok32 (2 * ((reveal qm).q_w + (reveal qm).q_h)))
  returns  v: I32.t
  ensures  quad__inv s #p qm **
           pure (I32.v v == (reveal qm).q_w + (reveal qm).q_h)
{
  let p2 = quad_perimeter s #p #qm;
  I32.div p2 2l
}


// =================================================================================
// 7. Leaf class `Square`, deriving from `Quadrilateral`
// =================================================================================

/// ```csharp
/// public sealed class Square : Quadrilateral {
///     private int side;
///     ...
/// }
/// ```
/// `Square` forgets through *two* levels: its own model has one number, the
/// quadrilateral model has two, and the shape model has one again. Only the first hop
/// is written here -- the second is `quad__forget`, and the composite is whatever the
/// derived `Shape` vtable does.
noeq type square__model = { s_side: int }

let square__forget (sm: square__model) : quad__model =
  { q_w = sm.s_side; q_h = sm.s_side }

noeq type square__raw = { fld_side: I32.t }
let square : Type0 = B.box square__raw

let square__inv (c: square) (#[T.exact (`1.0R)] p: perm) (sm: square__model) : slprop =
  exists* (r: square__raw).
    B.pts_to c #p r **
    pure (I32.v r.fld_side == sm.s_side /\ 1 <= sm.s_side)

/// The quadrilateral invariant as `Square` implements it. `ok32 (quad__forget qm)` is
/// `Square`'s standing class invariant: its area is representable.
let square__as_quad (c: square) (#[T.exact (`1.0R)] p: perm) (qm: quad__model) : slprop =
  exists* (sm: square__model).
    square__inv c #p sm **
    pure (square__forget sm == qm /\ ok32 (quad__forget qm))

fn square_area (c: square) (#p: perm) (#qm: erased quad__model)
  preserves square__as_quad c #p qm
  returns v: I32.t
  ensures pure (I32.v v == quad__forget qm)
{
  unfold (square__as_quad c #p qm);
  with sm. assert (square__inv c #p sm);
  unfold (square__inv c #p sm);
  let r = B.op_Bang c;
  let a = I32.mul r.fld_side r.fld_side;
  fold (square__inv c #p sm);
  fold (square__as_quad c #p qm);
  a
}

fn square_dbl (c: square) (#qm: erased quad__model)
  requires square__as_quad c #1.0R qm ** pure (ok32 (4 * quad__forget qm))
  ensures  square__as_quad c #1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h })
{
  unfold (square__as_quad c #1.0R qm);
  with sm. assert (square__inv c #1.0R sm);
  unfold (square__inv c #1.0R sm);
  double_fits 1 sm.s_side;
  let r = B.op_Bang c;
  let s2 = I32.mul r.fld_side 2l;
  B.op_Colon_Equals c { fld_side = s2 };
  fold (square__inv c #1.0R ({ s_side = 2 * sm.s_side }));
  fold (square__as_quad c #1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h }));
}

fn square_perim (c: square) (#p: perm) (#qm: erased quad__model)
  requires square__as_quad c #p qm **
           pure (ok32 (2 * ((reveal qm).q_w + (reveal qm).q_h)))
  returns  v: I32.t
  ensures  square__as_quad c #p qm **
           pure (I32.v v == 2 * ((reveal qm).q_w + (reveal qm).q_h))
{
  unfold (square__as_quad c #p qm);
  with sm. assert (square__inv c #p sm);
  unfold (square__inv c #p sm);
  let r = B.op_Bang c;
  let v = I32.mul r.fld_side 4l;
  fold (square__inv c #p sm);
  fold (square__as_quad c #p qm);
  v
}

ghost fn square_share (c: square) (#p: perm) (#qm: erased quad__model)
  requires square__as_quad c #p qm
  ensures  square__as_quad c #(p /. 2.0R) qm ** square__as_quad c #(p /. 2.0R) qm
{
  unfold (square__as_quad c #p qm);
  with sm. assert (square__inv c #p sm);
  unfold (square__inv c #p sm);
  with r. assert (B.pts_to c #p r);
  B.share c;
  fold (square__inv c #(p /. 2.0R) sm);
  fold (square__inv c #(p /. 2.0R) sm);
  fold (square__as_quad c #(p /. 2.0R) qm);
  fold (square__as_quad c #(p /. 2.0R) qm);
}

[@@allow_ambiguous]
ghost fn square_gather (c: square) (p: perm) (q: perm)
                       (#qm: erased quad__model) (#qm2: erased quad__model)
  requires square__as_quad c #p qm ** square__as_quad c #q qm2
  ensures  square__as_quad c #(p +. q) qm ** pure (reveal qm == reveal qm2)
{
  unfold (square__as_quad c #p qm);
  with sm. assert (square__inv c #p sm);
  unfold (square__inv c #p sm);
  with r. assert (B.pts_to c #p r);

  unfold (square__as_quad c #q qm2);
  with sm2. assert (square__inv c #q sm2);
  unfold (square__inv c #q sm2);
  with r2. assert (B.pts_to c #q r2);

  B.pts_to_injective_eq c;
  rewrite (B.pts_to c #q r2) as (B.pts_to c #q r);
  B.gather c;
  fold (square__inv c #(p +. q) sm);
  fold (square__as_quad c #(p +. q) qm);
}

/// `Square` packs a **quadrilateral** vtable, and nothing else. Its `Shape` vtable is
/// `quad_as_shape_pkg t_square`, which it never writes.
let t_square : t_quad = {
  qimpl   = square;
  qinv    = (fun c p qm -> square__as_quad c #p qm);
  qarea   = (fun c #p #qm -> square_area c #p #qm);
  qdbl    = (fun c #qm -> square_dbl c #qm);
  qperim  = (fun c #p #qm -> square_perim c #p #qm);
  qshare  = (fun c #p #qm -> square_share c #p #qm);
  qgather = (fun c p q #qm #qm2 -> square_gather c p q #qm #qm2);
}

let square__obj (c: square) : quad__obj = { qpkg = t_square; qrep = c }

/// ```csharp
/// Quadrilateral q = sq;     // sq : Square
/// ```
/// The upcast across the *outer* edge. Composing it with `upcast_quad` gets a `Shape`.
ghost fn upcast_square_at (c: square) (#p: perm) (#qm: erased quad__model)
  requires square__as_quad c #p qm
  ensures  quad__inv_at (Dn.mkdyn (shape_view (square__obj c)))
                        (hide (square__obj c)) p qm
{
  rewrite (square__as_quad c #p qm) as (quad__at (square__obj c) p qm);
  fold (quad__inv_at (Dn.mkdyn (shape_view (square__obj c)))
                     (hide (square__obj c)) p qm);
}

/// The same upcast with the implementation forgotten -- which is what a client that
/// will never downcast wants, and what makes `Square` and `Rectangle` interchangeable.
ghost fn upcast_square (c: square) (#p: perm) (#qm: erased quad__model)
  requires square__as_quad c #p qm
  ensures  quad__inv (Dn.mkdyn (shape_view (square__obj c))) #p qm
{
  upcast_square_at c #p #qm;
  quad_forget_impl (Dn.mkdyn (shape_view (square__obj c))) (hide (square__obj c));
}

/// ```csharp
/// Quadrilateral q = new Square(n);
/// ```
fn new_square (n: I32.t)
  requires pure (1 <= I32.v n /\ ok32 (I32.v n * I32.v n))
  returns  s: shape
  ensures  quad__inv s #1.0R ({ q_w = I32.v n; q_h = I32.v n })
{
  let c = B.alloc ({ fld_side = n });
  fold (square__inv c #1.0R ({ s_side = I32.v n }));
  fold (square__as_quad c #1.0R ({ q_w = I32.v n; q_h = I32.v n }));
  upcast_square c;
  Dn.mkdyn (shape_view (square__obj c))
}


// =================================================================================
// 8. Leaf class `Rectangle`, deriving from `Quadrilateral`
// =================================================================================

/// Doubling both sides of a rectangle cannot overflow if the *quadrupled area* does
/// not, provided neither side is degenerate. `double_fits` is this lemma's square case;
/// this is the general one, and it is again the only nonlinear step.
let rect_double_fits (w: int) (h: int)
  : Lemma (requires 1 <= w /\ 1 <= h /\ ok32 (4 * (w * h)))
          (ensures  ok32 (2 * w) /\ ok32 (2 * h))
  = FStar.Math.Lemmas.lemma_mult_le_right w 2 (4 * h);
    assert (2 * w <= (4 * h) * w);
    FStar.Math.Lemmas.lemma_mult_le_right h 2 (4 * w);
    assert (2 * h <= (4 * w) * h)

/// ```csharp
/// public sealed class Rectangle : Quadrilateral {
///     private int width, height;
///     ...
/// }
/// ```
/// A sibling of `Square` whose model happens to carry the same information as
/// `Quadrilateral`'s, so its forgetful map is essentially the identity. The encoding
/// neither requires a subclass to extend the model nor forbids it -- what it requires is
/// only that *some* pure map exists.
noeq type rect__model = { r_w: int; r_h: int }

let rect__forget (rm: rect__model) : quad__model = { q_w = rm.r_w; q_h = rm.r_h }

noeq type rect__raw = { fld_w: I32.t; fld_h: I32.t }
let rect : Type0 = B.box rect__raw

let rect__inv (c: rect) (#[T.exact (`1.0R)] p: perm) (rm: rect__model) : slprop =
  exists* (r: rect__raw).
    B.pts_to c #p r **
    pure (I32.v r.fld_w == rm.r_w /\ I32.v r.fld_h == rm.r_h /\ 1 <= rm.r_w /\ 1 <= rm.r_h)

let rect__as_quad (c: rect) (#[T.exact (`1.0R)] p: perm) (qm: quad__model) : slprop =
  exists* (rm: rect__model).
    rect__inv c #p rm **
    pure (rect__forget rm == qm /\ ok32 (quad__forget qm))

fn rect_area (c: rect) (#p: perm) (#qm: erased quad__model)
  preserves rect__as_quad c #p qm
  returns v: I32.t
  ensures pure (I32.v v == quad__forget qm)
{
  unfold (rect__as_quad c #p qm);
  with rm. assert (rect__inv c #p rm);
  unfold (rect__inv c #p rm);
  let r = B.op_Bang c;
  let a = I32.mul r.fld_w r.fld_h;
  fold (rect__inv c #p rm);
  fold (rect__as_quad c #p qm);
  a
}

fn rect_dbl (c: rect) (#qm: erased quad__model)
  requires rect__as_quad c #1.0R qm ** pure (ok32 (4 * quad__forget qm))
  ensures  rect__as_quad c #1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h })
{
  unfold (rect__as_quad c #1.0R qm);
  with rm. assert (rect__inv c #1.0R rm);
  unfold (rect__inv c #1.0R rm);
  rect_double_fits rm.r_w rm.r_h;
  let r = B.op_Bang c;
  let w2 = I32.mul r.fld_w 2l;
  let h2 = I32.mul r.fld_h 2l;
  B.op_Colon_Equals c { fld_w = w2; fld_h = h2 };
  fold (rect__inv c #1.0R ({ r_w = 2 * rm.r_w; r_h = 2 * rm.r_h }));
  fold (rect__as_quad c #1.0R ({ q_w = 2 * (reveal qm).q_w; q_h = 2 * (reveal qm).q_h }));
}

fn rect_perim (c: rect) (#p: perm) (#qm: erased quad__model)
  requires rect__as_quad c #p qm **
           pure (ok32 (2 * ((reveal qm).q_w + (reveal qm).q_h)))
  returns  v: I32.t
  ensures  rect__as_quad c #p qm **
           pure (I32.v v == 2 * ((reveal qm).q_w + (reveal qm).q_h))
{
  unfold (rect__as_quad c #p qm);
  with rm. assert (rect__inv c #p rm);
  unfold (rect__inv c #p rm);
  let r = B.op_Bang c;
  let sum = I32.add r.fld_w r.fld_h;
  let v = I32.mul sum 2l;
  fold (rect__inv c #p rm);
  fold (rect__as_quad c #p qm);
  v
}

ghost fn rect_share (c: rect) (#p: perm) (#qm: erased quad__model)
  requires rect__as_quad c #p qm
  ensures  rect__as_quad c #(p /. 2.0R) qm ** rect__as_quad c #(p /. 2.0R) qm
{
  unfold (rect__as_quad c #p qm);
  with rm. assert (rect__inv c #p rm);
  unfold (rect__inv c #p rm);
  with r. assert (B.pts_to c #p r);
  B.share c;
  fold (rect__inv c #(p /. 2.0R) rm);
  fold (rect__inv c #(p /. 2.0R) rm);
  fold (rect__as_quad c #(p /. 2.0R) qm);
  fold (rect__as_quad c #(p /. 2.0R) qm);
}

[@@allow_ambiguous]
ghost fn rect_gather (c: rect) (p: perm) (q: perm)
                     (#qm: erased quad__model) (#qm2: erased quad__model)
  requires rect__as_quad c #p qm ** rect__as_quad c #q qm2
  ensures  rect__as_quad c #(p +. q) qm ** pure (reveal qm == reveal qm2)
{
  unfold (rect__as_quad c #p qm);
  with rm. assert (rect__inv c #p rm);
  unfold (rect__inv c #p rm);
  with r. assert (B.pts_to c #p r);

  unfold (rect__as_quad c #q qm2);
  with rm2. assert (rect__inv c #q rm2);
  unfold (rect__inv c #q rm2);
  with r2. assert (B.pts_to c #q r2);

  B.pts_to_injective_eq c;
  rewrite (B.pts_to c #q r2) as (B.pts_to c #q r);
  B.gather c;
  fold (rect__inv c #(p +. q) rm);
  fold (rect__as_quad c #(p +. q) qm);
}

let t_rect : t_quad = {
  qimpl   = rect;
  qinv    = (fun c p qm -> rect__as_quad c #p qm);
  qarea   = (fun c #p #qm -> rect_area c #p #qm);
  qdbl    = (fun c #qm -> rect_dbl c #qm);
  qperim  = (fun c #p #qm -> rect_perim c #p #qm);
  qshare  = (fun c #p #qm -> rect_share c #p #qm);
  qgather = (fun c p q #qm #qm2 -> rect_gather c p q #qm #qm2);
}

let rect__obj (c: rect) : quad__obj = { qpkg = t_rect; qrep = c }

ghost fn upcast_rect_at (c: rect) (#p: perm) (#qm: erased quad__model)
  requires rect__as_quad c #p qm
  ensures  quad__inv_at (Dn.mkdyn (shape_view (rect__obj c))) (hide (rect__obj c)) p qm
{
  rewrite (rect__as_quad c #p qm) as (quad__at (rect__obj c) p qm);
  fold (quad__inv_at (Dn.mkdyn (shape_view (rect__obj c))) (hide (rect__obj c)) p qm);
}

ghost fn upcast_rect (c: rect) (#p: perm) (#qm: erased quad__model)
  requires rect__as_quad c #p qm
  ensures  quad__inv (Dn.mkdyn (shape_view (rect__obj c))) #p qm
{
  upcast_rect_at c #p #qm;
  quad_forget_impl (Dn.mkdyn (shape_view (rect__obj c))) (hide (rect__obj c));
}

/// ```csharp
/// Quadrilateral q = new Rectangle(w, h);
/// ```
fn new_rect (w: I32.t) (h: I32.t)
  requires pure (1 <= I32.v w /\ 1 <= I32.v h /\ ok32 (I32.v w * I32.v h))
  returns  s: shape
  ensures  quad__inv s #1.0R ({ q_w = I32.v w; q_h = I32.v h })
{
  let c = B.alloc ({ fld_w = w; fld_h = h });
  fold (rect__inv c #1.0R ({ r_w = I32.v w; r_h = I32.v h }));
  fold (rect__as_quad c #1.0R ({ q_w = I32.v w; q_h = I32.v h }));
  upcast_rect c;
  Dn.mkdyn (shape_view (rect__obj c))
}


// =================================================================================
// 9. A heterogeneous `Shape[]`
// =================================================================================

/// ```csharp
/// Shape[] shapes;
/// ```
/// An array of `Shape` needs *two* resources: `A.pts_to` for the references
/// themselves, and one object invariant per element. There is no way to fold the
/// second into the first -- `A.pts_to` says what the slots contain, not what those
/// contents own -- so the element invariants are carried beside it, as a separating
/// conjunction indexed by position.
///
/// `Pulse.Lib.ForEvery.Range`'s `forall+` over a contiguous range of `nat` is exactly
/// that conjunction, and it comes with the peel/append/borrow lemmas a loop needs.
/// `shape_slot` is total on all of `nat`, as `forall+` requires, so it is `emp`
/// outside the array.
let shape_slot (s: Seq.seq shape) (ms: Seq.seq shape__model) (p: perm) (k: nat) : slprop =
  if k < Seq.length s && k < Seq.length ms
  then shape__inv (Seq.index s k) #p (Seq.index ms k)
  else emp

/// The pure model of the whole array's areas, summed over a prefix.
let rec area_sum (ms: Seq.seq shape__model) (i: nat) : Tot int (decreases i) =
  if i = 0 then 0
  else area_sum ms (i - 1) + (if i - 1 < Seq.length ms then Seq.index ms (i - 1) else 0)

let nonneg (ms: Seq.seq shape__model) : prop =
  forall (k: nat). k < Seq.length ms ==> 0 <= Seq.index ms k

let rec area_sum_nonneg (ms: Seq.seq shape__model) (i: nat)
  : Lemma (requires nonneg ms) (ensures 0 <= area_sum ms i) (decreases i)
  = if i = 0 then () else area_sum_nonneg ms (i - 1)

/// Partial sums are monotone, which is what bounds the accumulator: if the total
/// fits in an `int`, so does every prefix.
let rec area_sum_mono (ms: Seq.seq shape__model) (i: nat) (j: nat)
  : Lemma (requires nonneg ms /\ i <= j) (ensures area_sum ms i <= area_sum ms j)
          (decreases j)
  = if i = j then () else (area_sum_mono ms i (j - 1); area_sum_nonneg ms (j - 1))


// =================================================================================
// 10. Read-only traversal
// =================================================================================

/// ```csharp
/// int total = 0;
/// for (int i = 0; i < shapes.Length; i++) total += shapes[i].Area();
/// ```
/// Each iteration *borrows* element `i` out of the conjunction with `range_focus`,
/// which hands back a trade to put it aside again. Nothing about the loop mentions
/// `Circle`, `Square`, `Rectangle` or even `Quadrilateral`: the call is dispatched
/// through the root vtable in the element, and the elements need not be at the same
/// depth in the hierarchy.
fn total_area (arr: CA.array shape) (n: I32.t { 0 <= I32.v n })
              (#q: perm) (#p: perm)
              (#s: erased (Seq.seq shape)) (#ms: erased (Seq.seq shape__model))
  requires A.pts_to arr #q s
        ** (forall+ (k:nat{0 <= k /\ k < I32.v n}). shape_slot s ms p k)
        ** pure (I32.v n == Seq.length s /\ Seq.length ms == Seq.length s /\
                 nonneg ms /\ ok32 (area_sum ms (I32.v n)))
  returns  v: I32.t
  ensures  A.pts_to arr #q s
        ** (forall+ (k:nat{0 <= k /\ k < I32.v n}). shape_slot s ms p k)
        ** pure (I32.v v == area_sum ms (I32.v n))
{
  let mut var_i = 0l;
  let mut var_acc = 0l;
  while (let t = !var_i; (I32.lt t n))
  invariant exists* vi vacc.
    R.pts_to var_i vi ** R.pts_to var_acc vacc **
    A.pts_to arr #q s **
    (forall+ (k:nat{0 <= k /\ k < I32.v n}). shape_slot s ms p k) **
    pure (0 <= I32.v vi /\ I32.v vi <= I32.v n /\
          I32.v vacc == area_sum ms (I32.v vi))
  decreases ((I32.v n) - (I32.v !var_i))
  {
    let i = !var_i;
    range_focus (shape_slot s ms p) 0 (I32.v i) (I32.v n);
    rewrite (shape_slot s ms p (I32.v i))
         as (shape__inv (Seq.index s (I32.v i)) #p (Seq.index ms (I32.v i)));
    let sh = CA.read arr i;
    let a = shape_area sh #p #(hide (Seq.index ms (I32.v i)));
    rewrite (shape__inv (Seq.index s (I32.v i)) #p (Seq.index ms (I32.v i)))
         as (shape_slot s ms p (I32.v i));
    Pulse.Lib.Trade.elim_trade
      (shape_slot s ms p (I32.v i))
      (op_forall_Plus #(k:nat{0 <= k /\ k < I32.v n}) (fun k -> shape_slot s ms p k));
    area_sum_mono ms (I32.v i + 1) (I32.v n);
    area_sum_nonneg ms (I32.v i + 1);
    let acc = !var_acc;
    var_acc := (I32.add acc a);
    var_i := (I32.add i 1l);
  };
  let r = !var_acc;
  r
}


// =================================================================================


// =================================================================================
// 11. A client polymorphic at the *intermediate* level
// =================================================================================

/// ```csharp
/// static int Spread(Quadrilateral a, Quadrilateral b)
///     => a.SemiPerimeter() + b.SemiPerimeter();
/// ```
/// This is what a three-level hierarchy is *for*: code written against
/// `Quadrilateral`, which works for `Square` and `Rectangle` alike, calls a method
/// `Shape` does not have, and keeps the bounding box in its specification. It names no
/// leaf class and would accept a subclass written after it.
fn spread (a: shape) (b: shape) (#p: perm)
          (#qa: erased quad__model) (#qb: erased quad__model)
  requires quad__inv a #p qa ** quad__inv b #p qb **
           pure (ok32 (2 * ((reveal qa).q_w + (reveal qa).q_h)) /\
                 ok32 (2 * ((reveal qb).q_w + (reveal qb).q_h)) /\
                 ok32 ((reveal qa).q_w + (reveal qa).q_h +
                       ((reveal qb).q_w + (reveal qb).q_h)))
  returns  v: I32.t
  ensures  quad__inv a #p qa ** quad__inv b #p qb **
           pure (I32.v v == (reveal qa).q_w + (reveal qa).q_h +
                            ((reveal qb).q_w + (reveal qb).q_h))
{
  let x = quad_semi_perimeter a #p #qa;
  let y = quad_semi_perimeter b #p #qb;
  I32.add x y
}


// =================================================================================
// 12. End-to-end client
// =================================================================================

/// `default(Shape)`, i.e. `null`. Still an open problem, and no more solved at depth
/// three than at depth two: `new Shape[3]` fills the array with a value of which no
/// object invariant holds.
let null_shape : shape = Dn.mkdyn ()

/// Areas of the three shapes built below: 3*2^2, 5^2, 3*4.
let demo_models : Seq.seq shape__model =
  Seq.upd (Seq.upd (Seq.upd (Seq.create 3 0) 0 12) 1 25) 2 12

/// ```csharp
/// Quadrilateral q1 = new Square(5);         // bounding box 5 x 5
/// Quadrilateral q2 = new Rectangle(3, 4);   // bounding box 3 x 4
/// int sp = Spread(q1, q2);                  // 10 + 7 == 17
///
/// Shape[] shapes = new Shape[3];
/// shapes[0] = new Circle(2);                // area 12
/// shapes[1] = q1;                           // area 25
/// shapes[2] = q2;                           // area 12
/// int area = TotalArea(shapes);             //      49
/// return sp + area;                         //      66
/// ```
/// The array is heterogeneous in two senses at once: its elements have three different
/// representations, and they sit at two different *depths* of the hierarchy. The
/// traversal cannot tell, because every element was made at the root object record.
fn demo ()
  requires emp
  returns  v: I32.t
  ensures  pure (I32.v v == 66)
{
  let s0 = new_circle 2l;
  let s1 = new_square 5l;
  let s2 = new_rect 3l 4l;

  // Used at the intermediate static type first: this call is impossible once the
  // references have been upcast to `Shape`, exactly as in C#.
  let sp = spread s1 s2 #1.0R
             #(hide ({ q_w = 5; q_h = 5 })) #(hide ({ q_w = 3; q_h = 4 }));
  assert (pure (I32.v sp == 17));

  // ```csharp
  // Shape sh1 = q1;   Shape sh2 = q2;
  // ```
  upcast_quad s1 #1.0R #(hide ({ q_w = 5; q_h = 5 }));
  upcast_quad s2 #1.0R #(hide ({ q_w = 3; q_h = 4 }));
  assert (shape__inv s1 #1.0R 25 ** shape__inv s2 #1.0R 12);

  let arr = CA.alloc #shape 3l null_shape;
  CA.write arr 0l s0;
  CA.write arr 1l s1;
  CA.write arr 2l s2;

  with sq. assert (A.pts_to arr sq);

  rewrite (shape__inv s2 #1.0R 12) as (shape_slot sq demo_models 1.0R 2);
  range_empty_intro (shape_slot sq demo_models 1.0R) 3;
  range_cons_down (shape_slot sq demo_models 1.0R) 3 3;

  rewrite (shape__inv s1 #1.0R 25) as (shape_slot sq demo_models 1.0R 1);
  range_cons_down (shape_slot sq demo_models 1.0R) 2 3;

  rewrite (shape__inv s0 #1.0R 12) as (shape_slot sq demo_models 1.0R 0);
  range_cons_down (shape_slot sq demo_models 1.0R) 1 3;

  range_rebound (shape_slot sq demo_models 1.0R) 0 3 0 (I32.v 3l);
  let area_all = total_area arr 3l #1.0R #1.0R #sq #demo_models;
  assert (pure (I32.v area_all == 49));

  drop_ (forall+ (k:nat{0 <= k /\ k < I32.v 3l}). shape_slot sq demo_models 1.0R k);
  drop_ (A.pts_to arr sq);
  I32.add sp area_all
}


// =================================================================================
// 13. What the encoding does *not* give you
// =================================================================================

/// ```csharp
/// Shape s = ...;
/// Quadrilateral q = (Quadrilateral) s;      // NOT modelled
/// ```
/// The upcasts above are all ghost, and rightly so. An **unchecked** downcast is not
/// merely non-ghost -- it is impossible.
///
/// Holding `shape__inv s #p m` tells you `s` is `mkdyn o` for some root object; it
/// tells you nothing about whether that object is the `shape_view` of a quadrilateral,
/// and no amount of separation logic will recover it -- the information was thrown away
/// by the existential when the reference was upcast, which is exactly what an upcast
/// means.
[@@expect_failure]
let downcast_is_not_free (s: shape) (o: shape__obj)
  : Lemma (requires s == Dn.mkdyn o)
          (ensures  exists (qo: quad__obj). o == shape_view qo)
  = ()

/// Section 14 gives the downcast a *precondition* instead, and gets it with no new
/// assumption. What is genuinely missing is a **failing** cast -- `q as Square`
/// returning `null`, or a checked cast throwing -- which is a runtime test whose
/// negative answer must be trusted, and so would need `recover` strengthened to report
/// a mismatch rather than merely to succeed. Nothing here needs it, and it is not
/// assumed.
///
/// Also untouched, and each a real question for a C# surface:
///
///   * `base.M()` -- calling the parent's implementation of an overridden method. The
///     vtable here holds one implementation per slot, so a subclass that wants its
///     parent's needs the parent to expose it as an ordinary `fn`, which is what the
///     CLR's non-virtual `call` instruction does.
///   * `protected` -- a member visible to subclasses and not to clients. Nothing in the
///     encoding distinguishes them; `t_quad` is either exported or it is not.
///   * a class that overrides some methods and inherits others. Every class here
///     supplies a full vtable, which is correct but says nothing about how an emitter
///     should *build* one from a partial `override` list.
///   * `abstract` classes with fields, and hence a constructor chain.


// =================================================================================
// 14. The checked downcast: `is` and `(Square) q`
// =================================================================================

/// Section 13 says the downcast throws information away and cannot be undone by
/// wishing. It can be undone by *remembering*, and that is what C#'s cast operators
/// really are: `(Square) q` succeeds exactly when the object's dynamic type is
/// `Square`, and a caller who cannot say why it should be is writing a cast that may
/// throw.
///
/// So the model is a downcast whose **precondition is the knowledge**, carried by
/// `quad__inv_at` -- the same ghost index `gather` needed.
///
/// Be precise about what that buys. `recover` has **no failure mode**: it is not "test
/// the header and maybe fail", it is "given a proof that the header matches, hand back
/// the value", and its argument is refined by `d == mkdyn x`. `quad__inv_at` carries
/// exactly that refinement at each hop, so the cast below cannot fail -- but not
/// because anything proves a runtime test succeeds. It cannot fail because the encoding
/// only lets you *write* the casts whose test is redundant. A cast that might fail is
/// not a cast this study proves safe; it is a cast this study cannot express (section
/// 13), and giving it a meaning needs `recover` strengthened to report a mismatch.
///
/// That is the right stance for a verifier -- a verified cast is one that cannot
/// throw -- but it is a restriction on the source language, not a theorem about C#.
///
/// The runtime part is a chain of `recover`s, one per level, because in this encoding
/// each level's object record is a *distinct value*. So the cast is **not** free at
/// runtime: depth `k` costs `k` recoveries where the CLR does one header check. What is
/// free is the *proof* -- no assumption beyond the `recover` already needed for ordinary
/// virtual dispatch. That difference is the price of erasing the dynamic type into
/// `dyn`, and it is paid in casts, not in memory.

/// The leaf representation, re-erased. Reading it out of the recovered object record
/// directly would need a coercion across `qo.qpkg.qimpl == square`, which is only
/// propositionally true; going back through `mkdyn` keeps everything a `dyn`, and
/// congruence on `quad_box` then delivers the equation the next `recover` wants.
let quad_box (qo: quad__obj) : Dn.dyn = Dn.mkdyn qo.qrep

/// The class-independent half of a downcast: walk the chain and hand back the leaf
/// representation, still erased. Every leaf's downcast is this plus one `recover`.
fn quad_rep (s: shape) (#qo: erased quad__obj) (#p: perm) (#qm: erased quad__model)
  preserves quad__inv_at s qo p qm
  returns  d: Dn.dyn
  ensures  pure (d == quad_box qo)
{
  unfold (quad__inv_at s qo p qm);
  let ob = recover #shape__obj #(hide (shape_view (reveal qo))) s;
  let qob = recover #quad__obj #qo ob.sub;
  fold (quad__inv_at s qo p qm);
  quad_box qob
}

/// ```csharp
/// Square sq = (Square) q;       // q : Quadrilateral, known to be a Square
/// ```
/// The precondition names the object the caller is holding, so the cast is justified
/// before it is written. The postcondition hands back `Square`'s own invariant, so
/// `Square`-only members become callable -- which is the only reason to downcast.
fn downcast_square (s: shape) (#c: erased square) (#p: perm) (#qm: erased quad__model)
  requires quad__inv_at s (hide (square__obj (reveal c))) p qm
  returns  r: square
  ensures  square__as_quad r #p qm ** pure (r == reveal c)
{
  let d = quad_rep s #(hide (square__obj (reveal c))) #p #qm;
  let r = recover #square #c d;
  unfold (quad__inv_at s (hide (square__obj (reveal c))) p qm);
  rewrite (quad__at (hide (square__obj (reveal c))) p qm) as (square__as_quad r #p qm);
  r
}

fn downcast_rect (s: shape) (#c: erased rect) (#p: perm) (#qm: erased quad__model)
  requires quad__inv_at s (hide (rect__obj (reveal c))) p qm
  returns  r: rect
  ensures  rect__as_quad r #p qm ** pure (r == reveal c)
{
  let d = quad_rep s #(hide (rect__obj (reveal c))) #p #qm;
  let r = recover #rect #c d;
  unfold (quad__inv_at s (hide (rect__obj (reveal c))) p qm);
  rewrite (quad__at (hide (rect__obj (reveal c))) p qm) as (rect__as_quad r #p qm);
  r
}

/// ```csharp
/// q is Square
/// ```
/// `is` is the *proposition* `downcast_square`'s precondition asks for, with the
/// witness left anonymous -- which is how a caller would naturally state it, since it
/// has no name for the box inside.
let is_square (qo: quad__obj) : prop = exists (c: square). qo == square__obj c

let is_rect (qo: quad__obj) : prop = exists (c: rect). qo == rect__obj c

/// Turning the proposition back into the named index. Ghost and free: the witness is
/// recovered by classical choice, never computed.
ghost fn as_square (s: shape) (#qo: erased quad__obj) (#p: perm) (#qm: erased quad__model)
  requires quad__inv_at s qo p qm ** pure (is_square qo)
  returns  c: erased square
  ensures  quad__inv_at s (hide (square__obj (reveal c))) p qm
{
  let c : erased square =
    hide (FStar.IndefiniteDescription.indefinite_description_ghost
            square (fun (c: square) -> reveal qo == square__obj c));
  rewrite (quad__inv_at s qo p qm)
       as (quad__inv_at s (hide (square__obj (reveal c))) p qm);
  c
}

/// A `Square`-only member: `Quadrilateral` has no name for a side, and this is what
/// the downcast was for.
///
/// ```csharp
/// [Ensures("Result == @this.W")] public int Side();     // in Square
/// ```
fn square_side (c: square) (#p: perm) (#qm: erased quad__model)
  preserves square__as_quad c #p qm
  returns v: I32.t
  ensures pure (I32.v v == (reveal qm).q_w)
{
  unfold (square__as_quad c #p qm);
  with sm. assert (square__inv c #p sm);
  unfold (square__inv c #p sm);
  let r = B.op_Bang c;
  let v = r.fld_side;
  fold (square__inv c #p sm);
  fold (square__as_quad c #p qm);
  v
}

/// A constructor that *keeps* the knowledge, so that a caller may downcast later.
/// `new_square` is this one with the index forgotten -- and forgetting it is what
/// makes the result interchangeable with a `Rectangle`.
fn new_square_at (n: I32.t)
  requires pure (1 <= I32.v n /\ ok32 (I32.v n * I32.v n))
  returns  s: shape
  ensures  exists* (c: square).
             quad__inv_at s (hide (square__obj c)) 1.0R
                          ({ q_w = I32.v n; q_h = I32.v n })
{
  let c = B.alloc ({ fld_side = n });
  fold (square__inv c #1.0R ({ s_side = I32.v n }));
  fold (square__as_quad c #1.0R ({ q_w = I32.v n; q_h = I32.v n }));
  upcast_square_at c;
  Dn.mkdyn (shape_view (square__obj c))
}

/// Forgetting the index is **irreversible**, even to a client that can say what the
/// index was. Unfolding `quad__inv s` yields some anonymous `qo'` with
/// `s == mkdyn (shape_view qo')`; the hypothesis gives `s == mkdyn (shape_view qo)`;
/// concluding `qo' == qo` is injectivity of `mkdyn`, which section 3 of
/// `ShapeHierarchy.fst` pins as unavailable. So a client really must decide at the
/// upcast whether it intends to come back, and that is the honest reading of C#: a
/// `Quadrilateral`-typed variable carries no static evidence of its dynamic type, and
/// recovering it needs a *runtime* test, which is exactly the strengthened axiom above.
[@@expect_failure]
ghost fn quad_remember_impl (s: shape) (qo: erased quad__obj)
                            (#p: perm) (#qm: erased quad__model)
  requires quad__inv s #p qm ** pure (s == Dn.mkdyn (shape_view (reveal qo)))
  ensures  quad__inv_at s qo p qm
{
  unfold (quad__inv s #p qm);
  fold (quad__inv_at s qo p qm);
}

/// And the knowledge cannot be *invented*: no `Rectangle` is a `Square`, but neither is
/// that provable here -- F\* has no general way to refute an equation between values of
/// two abstract representation types, so `is_square` on a rectangle is simply
/// undecided. That is sound (the caller still cannot downcast) and is the right pin:
/// what makes a cast safe in this encoding is a *positive* record of the construction,
/// never the failure of an attempt to disprove it.
[@@expect_failure]
let a_rectangle_is_not_a_square (c: rect)
  : Lemma (~ (is_square (rect__obj c)))
  = ()

/// ```csharp
/// Quadrilateral q = new Square(7);
/// int a    = q.Area();          // 49, dispatched at Quadrilateral
/// Square sq = (Square) q;       // checked cast, justified by construction
/// int side  = sq.Side();        // 7,  a Square-only member
/// return a + side;              // 56
/// ```
/// The whole point in one function: the reference is used at the intermediate static
/// type, then narrowed, then used at the leaf type -- and the narrowing is justified by
/// what the client did to build the object, not by a test it hopes will pass.
fn downcast_demo ()
  requires emp
  returns  v: I32.t
  ensures  pure (I32.v v == 56)
{
  let s = new_square_at 7l;
  let a = quad_area_at s;
  let sq = downcast_square s;
  let side = square_side sq;
  drop_ (square__as_quad sq #1.0R ({ q_w = 7; q_h = 7 }));
  I32.add a side
}
