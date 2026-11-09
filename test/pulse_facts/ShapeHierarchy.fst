module ShapeHierarchy

/// A worked design study: a `Shape` / `Circle` / `Square` hierarchy in Pulse, written
/// directly, in the encoding F28-F34 of doc/translation.md were probed for.
///
/// This is not a translation target and not a golden file. It exists to settle the
/// Pulse-level design *before* any C# surface syntax or emitter rule is committed to,
/// as doc/translation.md section 0 requires. Every construct here is one a translation
/// would have to produce, and each is annotated with the C# it stands for.
///
/// What it demonstrates:
///
///   * an abstract class `Shape` with two virtual methods, one read-only and one
///     mutating, dispatched dynamically;
///   * two subclasses with *different representations* and *different model types*,
///     each relating to the base model by a forgetful map;
///   * constructors returning a value of the base static type;
///   * a heterogeneous `Shape[]`, with per-element object invariants carried
///     alongside the array's own ownership;
///   * clients that traverse the array, dispatching virtually on each element --
///     one read-only, one mutating.

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
noeq type shape__obj = { pkg: t_shape; rep: pkg.impl }

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
  ensures  shape__inv (Dn.mkdyn ({ pkg = t_circle; rep = c } <: shape__obj)) #p m
{
  rewrite (circle__as_shape c #p m)
       as (shape__at ({ pkg = t_circle; rep = c } <: shape__obj) p m);
  fold (shape__inv (Dn.mkdyn ({ pkg = t_circle; rep = c } <: shape__obj)) #p m);
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
  Dn.mkdyn ({ pkg = t_circle; rep = c } <: shape__obj)
}


// =================================================================================
// 5. Subclass `Square`
// =================================================================================

/// A second implementation whose representation is a different record entirely, to
/// check that nothing above quietly assumed a common layout.
noeq type square__model = { s_side: int }
let square__forget (sm: square__model) : shape__model = sm.s_side * sm.s_side

noeq type square__raw = { fld_side: I32.t }
let square : Type0 = B.box square__raw

let square__inv (q: square) (#[T.exact (`1.0R)] p: perm) (sm: square__model) : slprop =
  exists* (r: square__raw).
    B.pts_to q #p r **
    pure (I32.v r.fld_side == sm.s_side /\ 0 <= sm.s_side)

let square__as_shape (q: square) (#[T.exact (`1.0R)] p: perm) (m: shape__model) : slprop =
  exists* (sm: square__model).
    square__inv q #p sm ** pure (square__forget sm == m /\ ok32 m)

fn square_area (q: square) (#p: perm) (#m: erased shape__model)
  preserves square__as_shape q #p m
  returns v: I32.t
  ensures pure (I32.v v == reveal m)
{
  unfold (square__as_shape q #p m);
  with sm. assert (square__inv q #p sm);
  unfold (square__inv q #p sm);
  let r = B.op_Bang q;
  let a = I32.mul r.fld_side r.fld_side;
  fold (square__inv q #p sm);
  fold (square__as_shape q #p m);
  a
}

fn square_double (q: square) (#m: erased shape__model)
  requires square__as_shape q #1.0R m ** pure (ok32 (4 * reveal m))
  ensures  square__as_shape q #1.0R (4 * reveal m)
{
  unfold (square__as_shape q #1.0R m);
  with sm. assert (square__inv q #1.0R sm);
  unfold (square__inv q #1.0R sm);
  double_fits 1 sm.s_side;
  let r = B.op_Bang q;
  let s2 = I32.mul r.fld_side 2l;
  B.op_Colon_Equals q { fld_side = s2 };
  fold (square__inv q #1.0R ({ s_side = 2 * sm.s_side }));
  fold (square__as_shape q #1.0R (4 * reveal m));
}

ghost fn square_share (q: square) (#p: perm) (#m: erased shape__model)
  requires square__as_shape q #p m
  ensures  square__as_shape q #(p /. 2.0R) m ** square__as_shape q #(p /. 2.0R) m
{
  unfold (square__as_shape q #p m);
  with sm. assert (square__inv q #p sm);
  unfold (square__inv q #p sm);
  with r. assert (B.pts_to q #p r);
  B.share q;
  assert (B.pts_to q #(p /. 2.0R) r ** B.pts_to q #(p /. 2.0R) r);
  fold (square__inv q #(p /. 2.0R) sm);
  fold (square__inv q #(p /. 2.0R) sm);
  fold (square__as_shape q #(p /. 2.0R) m);
  fold (square__as_shape q #(p /. 2.0R) m);
}

[@@allow_ambiguous]
ghost fn square_gather (q: square) (p1 p2: perm)
                       (#m: erased shape__model) (#m2: erased shape__model)
  requires square__as_shape q #p1 m ** square__as_shape q #p2 m2
  ensures  square__as_shape q #(p1 +. p2) m ** pure (reveal m == reveal m2)
{
  unfold (square__as_shape q #p1 m);
  with sm. assert (square__inv q #p1 sm);
  unfold (square__inv q #p1 sm);
  with r. assert (B.pts_to q #p1 r);

  unfold (square__as_shape q #p2 m2);
  with sm2. assert (square__inv q #p2 sm2);
  unfold (square__inv q #p2 sm2);
  with r2. assert (B.pts_to q #p2 r2);

  B.pts_to_injective_eq q;
  rewrite (B.pts_to q #p2 r2) as (B.pts_to q #p2 r);
  B.gather q;
  assert (pure (sm == sm2));
  fold (square__inv q #(p1 +. p2) sm);
  fold (square__as_shape q #(p1 +. p2) m);
}

let t_square : t_shape = {
  impl = square;
  inv  = (fun q p m -> square__as_shape q #p m);
  area = square_area;
  dbl  = square_double;
  share = square_share;
  gather = square_gather;
}

ghost fn upcast_square (q: square) (#p: perm) (#m: erased shape__model)
  requires square__as_shape q #p m
  ensures  shape__inv (Dn.mkdyn ({ pkg = t_square; rep = q } <: shape__obj)) #p m
{
  rewrite (square__as_shape q #p m)
       as (shape__at ({ pkg = t_square; rep = q } <: shape__obj) p m);
  fold (shape__inv (Dn.mkdyn ({ pkg = t_square; rep = q } <: shape__obj)) #p m);
}

fn new_square (side: I32.t)
  requires pure (0 <= I32.v side /\ ok32 (I32.v side * I32.v side))
  returns  s: shape
  ensures  shape__inv s #1.0R (I32.v side * I32.v side)
{
  let q = B.alloc ({ fld_side = side });
  fold (square__inv q #1.0R ({ s_side = I32.v side }));
  fold (square__as_shape q #1.0R (I32.v side * I32.v side));
  upcast_square q;
  Dn.mkdyn ({ pkg = t_square; rep = q } <: shape__obj)
}


// =================================================================================
// 6. A heterogeneous `Shape[]`
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
// 7. Read-only traversal
// =================================================================================

/// ```csharp
/// int total = 0;
/// for (int i = 0; i < shapes.Length; i++) total += shapes[i].Area();
/// ```
/// Each iteration *borrows* element `i` out of the conjunction with `range_focus`,
/// which hands back a trade to put it aside again. Nothing about the loop mentions
/// `Circle` or `Square`: the call is dispatched through the vtable in the element.
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
// 8. Mutating traversal
// =================================================================================

/// The models after every shape has been doubled.
let quad (ms: Seq.seq shape__model) : Seq.seq shape__model =
  Seq.init (Seq.length ms) (fun i -> 4 * Seq.index ms i)

/// ```csharp
/// for (int i = 0; i < shapes.Length; i++) shapes[i].Double();
/// ```
/// The mutating case cannot borrow: the element's model *changes*, so the slprop put
/// back is not the one taken out and a trade would not close. Instead the loop carries
/// two ranges -- `[0,i)` already doubled and `[i,n)` not yet -- peeling from the front
/// of the second and appending to the back of the first.
///
/// Note what is *not* here: no case analysis on the dynamic type, and no mention of
/// `Circle` or `Square`. The array holds both and the loop is blind to which.
fn double_all (arr: CA.array shape) (n: I32.t { 0 <= I32.v n })
               (#q: perm)
               (#s: erased (Seq.seq shape)) (#ms: erased (Seq.seq shape__model))
  requires A.pts_to arr #q s
        ** (forall+ (k:nat{0 <= k /\ k < I32.v n}). shape_slot s ms 1.0R k)
        ** pure (I32.v n == Seq.length s /\ Seq.length ms == Seq.length s /\
                 (forall (k:nat). k < Seq.length ms ==> ok32 (4 * Seq.index ms k)))
  ensures  A.pts_to arr #q s
        ** (forall+ (k:nat{0 <= k /\ k < I32.v n}). shape_slot s (quad ms) 1.0R k)
{
  let mut var_i = 0l;
  range_empty_intro (shape_slot s (quad ms) 1.0R) 0;
  while (let t = !var_i; (I32.lt t n))
  invariant exists* vi.
    R.pts_to var_i vi ** A.pts_to arr #q s **
    (forall+ (k:nat{0 <= k /\ k < I32.v vi}). shape_slot s (quad ms) 1.0R k) **
    (forall+ (k:nat{I32.v vi <= k /\ k < I32.v n}). shape_slot s ms 1.0R k) **
    pure (0 <= I32.v vi /\ I32.v vi <= I32.v n)
  decreases ((I32.v n) - (I32.v !var_i))
  {
    let i = !var_i;
    range_uncons (shape_slot s ms 1.0R) (I32.v i) (I32.v n);
    rewrite (shape_slot s ms 1.0R (I32.v i))
         as (shape__inv (Seq.index s (I32.v i)) #1.0R (Seq.index ms (I32.v i)));
    let sh = CA.read arr i;
    shape_double sh #(hide (Seq.index ms (I32.v i)));
    rewrite (shape__inv (Seq.index s (I32.v i)) #1.0R (4 * Seq.index ms (I32.v i)))
         as (shape_slot s (quad ms) 1.0R (I32.v i));
    range_snoc (shape_slot s (quad ms) 1.0R) 0 (I32.v i);
    let i1 = (I32.add i 1l);
    range_rebound (shape_slot s (quad ms) 1.0R) 0 (I32.v i + 1) 0 (I32.v i1);
    range_rebound (shape_slot s ms 1.0R) (I32.v i + 1) (I32.v n) (I32.v i1) (I32.v n);
    var_i := i1;
  };
  with vi. assert (forall+ (k:nat{I32.v vi <= k /\ k < I32.v n}). shape_slot s ms 1.0R k);
  range_rebound (shape_slot s ms 1.0R) (I32.v vi) (I32.v n) (I32.v n) (I32.v n);
  range_empty_elim (shape_slot s ms 1.0R) (I32.v n);
  range_rebound (shape_slot s (quad ms) 1.0R) 0 (I32.v vi) 0 (I32.v n);
}


// =================================================================================
// 9. End-to-end client
// =================================================================================

/// `default(Shape)`, i.e. `null`. `new Shape[3]` fills the array with it, and no
/// object invariant holds of it -- which is exactly right: the element resources only
/// come into existence as the slots are assigned. A C# surface would have to account
/// for this, either by requiring definite assignment before the array is usable or by
/// modelling `null` explicitly.
let null_shape : shape = Dn.mkdyn ()

/// Areas of the three shapes built below: 3*2^2, 5^2, 3*1^2.
let demo_models : Seq.seq shape__model =
  Seq.upd (Seq.upd (Seq.upd (Seq.create 3 0) 0 12) 1 25) 2 3

/// ```csharp
/// Shape[] shapes = new Shape[3];
/// shapes[0] = new Circle(2);            // area  12
/// shapes[1] = new Square(5);            // area  25
/// shapes[2] = new Circle(1);            // area   3
/// int before = TotalArea(shapes);       //       40
/// DoubleAll(shapes);
/// int after  = TotalArea(shapes);       //      160
/// ```
fn demo ()
  requires emp
  returns  v: I32.t
  ensures  pure (I32.v v == 160)
{
  let s0 = new_circle 2l;
  let s1 = new_square 5l;
  let s2 = new_circle 1l;

  let arr = CA.alloc #shape 3l null_shape;
  CA.write arr 0l s0;
  CA.write arr 1l s1;
  CA.write arr 2l s2;

  with sq. assert (A.pts_to arr sq);

  rewrite (shape__inv s2 #1.0R 3)  as (shape_slot sq demo_models 1.0R 2);
  range_empty_intro (shape_slot sq demo_models 1.0R) 3;
  range_cons_down (shape_slot sq demo_models 1.0R) 3 3;

  rewrite (shape__inv s1 #1.0R 25) as (shape_slot sq demo_models 1.0R 1);
  range_cons_down (shape_slot sq demo_models 1.0R) 2 3;

  rewrite (shape__inv s0 #1.0R 12) as (shape_slot sq demo_models 1.0R 0);
  range_cons_down (shape_slot sq demo_models 1.0R) 1 3;

  range_rebound (shape_slot sq demo_models 1.0R) 0 3 0 (I32.v 3l);
  let before = total_area arr 3l #1.0R #1.0R #sq #demo_models;
  assert (pure (I32.v before == 40));

  double_all arr 3l #1.0R #sq #demo_models;
  let after = total_area arr 3l #1.0R #1.0R #sq #(quad demo_models);

  drop_ (forall+ (k:nat{0 <= k /\ k < I32.v 3l}). shape_slot sq (quad demo_models) 1.0R k);
  drop_ (A.pts_to arr sq);
  after
}


// =================================================================================
// 10. Read-only aliasing of a Shape
// =================================================================================

/// ```csharp
/// var c = new Circle(3);        // Shape c
/// Pal.Share(c);                 // ghost: two half-permission views
/// int a1 = c.Area();            // both readers see the same model
/// int a2 = c.Area();
/// Pal.Gather(c);                // ghost: back to full permission
/// c.Double();                   // ...so mutation is available again
/// ```
///
/// This is the whole point of the fractional index: two aliases of one `Shape` may be
/// read concurrently, and recombining them restores the write permission. Nothing here
/// costs anything at runtime -- `share` and `gather` are ghost, and the two "aliases"
/// are the same reference.
fn alias_demo ()
  requires emp
  returns  v: I32.t
  ensures  pure (I32.v v == 108)
{
  let s = new_circle 3l;
  assert (shape__inv s #1.0R 27);

  // Name the implementation package once; from here on stay at the indexed invariant.
  unfold (shape__inv s #1.0R 27);
  with o. assert (shape__at o 1.0R 27);
  fold (shape__inv_at s o 1.0R 27);

  shape_share_at s o #1.0R #(hide 27);

  // Two independent readers, each holding half the permission.
  let a1 = shape_area_at s #o #(1.0R /. 2.0R) #(hide 27);
  let a2 = shape_area_at s #o #(1.0R /. 2.0R) #(hide 27);
  assert (pure (I32.v a1 == 27 /\ I32.v a2 == 27));

  // Recombine, and the write permission is back.
  shape_gather_at s o (1.0R /. 2.0R) (1.0R /. 2.0R) #(hide 27) #(hide 27);
  assert (shape__inv_at s o (1.0R /. 2.0R +. 1.0R /. 2.0R) 27);
  rewrite (shape__inv_at s o (1.0R /. 2.0R +. 1.0R /. 2.0R) 27)
       as (shape__inv_at s o 1.0R 27);

  shape_forget_impl s o #1.0R #(hide 27);
  shape_double s #(hide 27);
  let v = shape_area s #1.0R #(hide 108);
  drop_ (shape__inv s #1.0R 108);
  v
}
