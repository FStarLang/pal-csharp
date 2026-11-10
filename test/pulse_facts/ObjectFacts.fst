module ObjectFacts

/// Regression tests for the object facts doc/translation.md R3.7-R3.13 depend on.
///
/// Like PulseFacts and StructFacts, these are NOT translation targets and NOT golden
/// files. They pin toolchain behaviour so that F13-F16 cannot silently regress under an
/// F* version bump. The shapes here are exactly the ones the emitter is specified to
/// produce for a `sealed class`.
///
/// The running example is the one M1 could not express at all: a class that *owns* an
/// array. `test/circular_buffer` had to pass its storage alongside the struct, because a
/// struct field of array type is PALCS0511 -- copying the struct would duplicate
/// ownership. A class is a heap cell, so it can own its array outright.

open Pulse
open Pulse.Lib.CSharp.Array

module A = Pulse.Lib.CSharp.Array
module B = Pulse.Lib.Box
open Pulse.Lib.Box { box, (!), (:=) }
module CA = Pulse.Lib.CSharp.Array
module I32 = FStar.Int32
module Seq = FStar.Seq
module T = FStar.Tactics

#lang-pulse

/// F14: `Pulse.Lib.Box` is the *sound* heap cell, and the right model of a CLR object.
///
///      `Pulse.Lib.Reference.alloc` carries
///          [@@deprecated "Reference.alloc is unsound; only use for model implementations"]
///      and so may not appear in generated code. `Box.alloc` carries no such marker: it
///      is an ordinary specified operation returning `b |-> x`.
///
/// F15: Pulse slprops are **affine**. `Box.free` exists but nothing compels a caller to
///      reach it -- a leftover resource is discharged by `drop_`. That is exactly the
///      CLR's garbage collector, so the object scheme needs no MODELING AXIOM at all:
///      the emitter allocates with `Box.alloc` and simply never emits `free`. Contrast
///      `Pulse.Lib.CSharp.Array.alloc`, which *did* need an axiom, because
///      `Pulse.Lib.Array.alloc` is a stack allocation that must not outlive its frame.
///
/// Both are pinned by `alloc_without_free` below, which allocates and returns without
/// freeing and *is accepted*.

/// The representation R3.7 emits for
///   `sealed class Stack { int[] items; int top; }`.
/// Field names are prefixed `fld_`, exactly as for a struct (R3.4), so the two share
/// their field-access and field-update rules verbatim.
noeq type class_Stack__raw = { fld_items: A.array I32.t; fld_top: I32.t }

/// R3.8: the object reference type is a `Box.box` of the representation.
let class_Stack = B.box class_Stack__raw

/// R3.9: the **model** of the object -- a pure ghost type, declared by the *user*, that
/// the invariant relates the implementation type to.
///
/// The model type is not derived by the compiler from the class's members. It is whatever
/// type the user's `[Model]` member returns, so it can be a type they already have a
/// theory about (`Seq<T>`, or a spec-only struct like this one), and pure lemmas about it
/// can be stated and proved without mentioning the implementation at all.
///
/// The one constraint is that the model must expose every observation a *caller* needs, to
/// establish a precondition as well as to exploit a postcondition. A bare `Seq.seq I32.t`
/// would be too weak here: capacity would stay trapped inside the invariant's existential,
/// a client could not state "the stack is not full", and `push` would be uncallable.
noeq type model_StackModel__raw = { elems: Seq.seq I32.t; capacity: nat }

/// F17: a fact about the **model alone** must live in the model's *type*, as a refinement,
///      and not in the object invariant -- otherwise no caller can use it.
///
/// This is the one place where `[Refine]` is right for a class, and it is the exact
/// complement of R3.10's rule that the *class* invariant must not be a refinement. The two
/// carry different kinds of fact and are not interchangeable:
///
///   * a fact relating the **fields** to each other or to the model (`0 <= top`,
///     `top <= length contents`, and the abstraction relation itself) is temporarily
///     breakable -- a method assigns one field, then the other -- so it belongs inside the
///     predicate, in the window `unfold`/`fold` marks;
///   * a fact about the **model** (`Count <= Capacity`) is a property of a pure ghost
///     value, so it is never breakable, and putting it inside the predicate hides it.
///
/// "Hides it" is literal, and is pinned by `client_sees_model_invariant` below. A caller
/// holds `class_Stack__inv this m` and, if the model type is unrefined, simply cannot
/// derive `Count m <= Capacity m` -- F* reports `Error 19` at the postcondition. It could
/// only recover the fact by unfolding the invariant, which defeats the abstraction and
/// would be impossible once R3.9's deferred `.fsti` step makes the predicate opaque.
/// With the refinement, the fact travels in the type of `m` and the client is free.
///
/// The obligation this creates is discharged where it should be: at the `fold` in `push`,
/// the emitter must show the model it constructs satisfies the refinement. That is a real
/// proof obligation, and it is the one that ties the two kinds of fact together -- the
/// representation-level invariant is exactly what makes the model-level one hold.
let model_StackModel__pred (m: model_StackModel__raw) : prop =
  Seq.length m.elems <= m.capacity

type model_StackModel = m: model_StackModel__raw { model_StackModel__pred m }

/// R3.10: the object invariant, **indexed by the model**.
///
/// This indexing is not decoration. With an un-indexed `inv (x: t) : slprop` the object's
/// entire state sits under an existential, so no postcondition could ever relate the
/// post-state to the pre-state -- every method spec would degrade to "the object is still
/// well formed", which is memory safety and nothing more. The index is what makes
/// functional correctness expressible.
///
/// Note also that the class invariant is a `pure` **conjunct inside** the predicate, not
/// a `[Refine]`-style refinement on `class_Stack__raw`. A refinement type must hold of
/// *every* value of the type, but R3.6 writes a whole record per field assignment, so a
/// method that transiently breaks its invariant between two field writes would be
/// rejected. Struct refinements are always true; class invariants are temporarily
/// breakable, and that difference is why they use different mechanisms.
let class_Stack__inv (this: class_Stack) (m: model_StackModel) : slprop =
  exists* (r: class_Stack__raw) (contents: Seq.seq I32.t).
    B.pts_to this r **
    A.pts_to r.fld_items contents **
    pure (0 <= I32.v r.fld_top /\ I32.v r.fld_top <= Seq.length contents /\
          Seq.length contents <= 2147483647 /\
          m.capacity == Seq.length contents /\
          m.elems == Seq.slice contents 0 (I32.v r.fld_top))

/// R3.9b: the **abstraction relation is inlined as a conjunct, with its bounds stated
/// first** -- it is not factored out as a separate `abs : raw -> contents -> model`.
///
/// This is forced, not stylistic. The abstraction is *partial*: `Seq.slice contents 0 (v
/// top)` is only well-typed once `0 <= v top <= Seq.length contents` is known. Factoring it
/// out as a total function would require refining its arguments, and that refinement would
/// then have to be discharged at *every* use of the model -- the identical trap R4.6 and
/// `test/insertion_sort_sorted` already recorded for `[Spec]` predicates carrying a
/// `[Requires]`. Inlining it costs nothing instead, because `p1 /\ p2` type-checks `p2`
/// with `p1` in scope, so the bounds conjuncts above make the `Seq.slice` well-typed
/// exactly where it appears. Conjunct order is therefore load-bearing.

/// R3.9c: a `[Spec]` member is a pure function **of the model**, never of the
/// representation.
///
/// This is what makes a contract like `[Requires("Count < Capacity")]` meaningful to a
/// caller: the caller holds `class_Stack__inv this m` and nothing else, so every spec-level
/// observation it mentions must be computable from `m` alone. A `[Spec]` member whose body
/// reads a field directly is therefore rejected (PALCS0523) with the advice to widen the
/// model -- which is precisely the diagnosis a user hitting the too-weak-model problem
/// needs, delivered at the declaration rather than as an unprovable call site.
let spec_Stack_Count    (m: model_StackModel) : int = Seq.length m.elems
let spec_Stack_Capacity (m: model_StackModel) : int = m.capacity

/// F17 (pinned). The client holds `class_Stack__inv this m` and nothing else, does not
/// unfold it, and still concludes a model-level fact. Weaken `model_StackModel__pred` to
/// `True` and this fails with
///     Error 19 at ObjectFacts.fst: (this: class_Stack) (m: erased model_StackModel)
/// which is what makes the refinement load-bearing rather than decorative.
fn client_sees_model_invariant (this: class_Stack) (#m: erased model_StackModel)
  preserves class_Stack__inv this m
  ensures  pure (spec_Stack_Count m <= spec_Stack_Capacity m)
{
  ()
}

/// F13: `preserves p` is a real `fn` spec clause in the pinned toolchain, and it composes
///      with `requires`/`ensures`. It is exactly `requires p ensures p`, so it is the
///      right -- and cheapest -- form for a **read-only** method, and *only* for one: on a
///      mutating method `preserves inv this` would be true but vacuous.
fn count (this: class_Stack) (#m: erased model_StackModel)
  preserves class_Stack__inv this m
  returns  n : I32.t
  ensures  pure (I32.v n == spec_Stack_Count m)
{
  unfold class_Stack__inv this m;
  let r = !this;
  fold class_Stack__inv this m;
  r.fld_top
}

/// R4.10: a mutating method threads the model through. The postcondition **existentially
/// quantifies the new model** and constrains it with the user's `[Ensures]` clauses,
/// interpreted over the new model and the old one.
///
/// It does *not* name the new model as a compiler-computed function of the old: the
/// emitter has no way to compute a model transformer in general, and inventing one would
/// be exactly the kind of proof step §0 forbids it from making. This is also the shape
/// arrays already use -- `ensures exists* post_a. A.pts_to var_a post_a ** pure (...)` --
/// so R4.10 threads a class's model precisely as R4.4 threads an array's, and `Old` needs
/// no new machinery.
fn push (this: class_Stack) (v: I32.t) (#m: erased model_StackModel)
  requires class_Stack__inv this m ** pure (spec_Stack_Count m < spec_Stack_Capacity m)
  ensures  exists* m'. class_Stack__inv this m' **
             pure (spec_Stack_Count m' == spec_Stack_Count m + 1 /\
                   spec_Stack_Capacity m' == spec_Stack_Capacity m /\
                   (reveal m').elems `Seq.equal` Seq.snoc (reveal m).elems v)
{
  unfold class_Stack__inv this m;
  let r = !this;
  CA.write r.fld_items r.fld_top v;
  this := { r with fld_top = I32.add r.fld_top 1l };
  with contents. assert (A.pts_to r.fld_items contents);
  fold class_Stack__inv this
    ({ elems = Seq.slice contents 0 (I32.v r.fld_top + 1); capacity = Seq.length contents });
}

/// R4.11 and F15: a constructor allocates, establishes the invariant, and returns the
/// object. Nothing frees either the array or the box; the function is accepted anyway,
/// which is the whole content of F15. Freshness is *free*: the frame rule gives every
/// caller `frame ** inv x m0`, so a newly constructed object is automatically separate
/// from everything that already existed. No emitter work is needed for that.
fn alloc_without_free (capacity: I32.t { I32.v capacity >= 0 })
  requires emp
  returns  x : class_Stack
  ensures  exists* m. class_Stack__inv x m **
             pure (spec_Stack_Count m == 0 /\ spec_Stack_Capacity m == I32.v capacity)
{
  let items = CA.alloc capacity 0l;
  let x = B.alloc ({ fld_items = items; fld_top = 0l });
  fold class_Stack__inv x ({ elems = Seq.empty; capacity = I32.v capacity });
  x
}

/// F16: an object resource is **linear**, so two owned parameters are necessarily
/// distinct objects. Aliasing is therefore not unsound, it is *unprovable* -- which is
/// the correct outcome, but produces a bare "Cannot prove: inv a _" that means nothing to
/// a C# programmer. The scheme accordingly requires a dedicated diagnostic (PALCS0520)
/// rather than letting F* report it.
///
/// The negative case is pinned by construction: `merge` below takes two objects, and
/// `merge a a` does not type-check. Uncomment the call to observe
///     Error 228: Tactic failed -- Cannot prove: class_Stack__inv a (*?u*)_
fn merge (a: class_Stack) (b: class_Stack) (#ma #mb: erased model_StackModel)
  preserves class_Stack__inv a ma
  preserves class_Stack__inv b mb
{
  ()
}

fn aliasing_is_unprovable (a: class_Stack) (#ma: erased model_StackModel)
  preserves class_Stack__inv a ma
{
  // merge a a;   // rejected: needs `inv a ma ** inv a ma`
  ()
}

/// F14 (continued): `Pulse.Lib.Box` already models a **nullable** CLR object reference, so R3.11
///      needs no new machinery for `null`.
///
///        `Box.null : box a`                        is C#'s `null`
///        `Box.is_null r : b:bool{b <==> r == null}` is `x == null`, and it is *pure*,
///                                                   so it may appear in a contract
///        `Box.pts_to_not_null`                      proves a live object is non-null
///
///      That last one is the load-bearing one: it says ownership *implies* non-nullness,
///      so a method holding `inv this m` never has to test for null, and R6.4's "no null
///      dereference" obligation is discharged by the invariant rather than by a check.
///      A C# `C?` maps to `box` with no non-null obligation; a `C` maps to `box` plus a
///      `pure (not (is_null x))` conjunct that `pts_to_not_null` supplies for free.
ghost
fn ownership_implies_non_null (this: class_Stack) (#m: erased model_StackModel)
  preserves class_Stack__inv this m
  ensures  pure (not (B.is_null this))
{
  unfold class_Stack__inv this m;
  B.pts_to_not_null this;
  fold class_Stack__inv this m;
}

/// F18: F15's affinity is a *permission* to discard, not an automatic discard. A method
/// that allocates an object and does not return it still holds the invariant when it
/// ends, and Pulse reports
///     Error 228: Leftover resources: class_Stack__inv x _
/// The discard has to be written, and writing it needs a name for the model the context
/// is holding -- which is an existential witness the emitter never chose. `with m.
/// assert p;` binds exactly that name, so the two-line idiom below is the whole of R4.14.
///
/// This is what the CLR's garbage collector translates to: not an axiom, and not nothing,
/// but a `drop_` the emitter must remember to emit at every exit.
fn allocate_and_discard (capacity: I32.t { I32.v capacity >= 0 })
  requires emp
  returns  n : I32.t
  ensures  pure (I32.v n == I32.v capacity)
{
  let x = alloc_without_free capacity;
  with m. assert (class_Stack__inv x m);
  drop_ (class_Stack__inv x m);
  capacity
}

/// F19: F18's idiom only works where the postcondition is *known*.
///
/// R4.14 discards an abandoned object at the end of the block that declares it. At the
/// end of a method that block's postcondition is the method's, and everything below
/// typechecks. Inside an `if` in statement position it is not: Pulse is still solving for
/// the branch's postcondition, the object's model is an existential in the context, and
/// unifying an existential against a uvar is exactly what it will not do --
///     Error 339: Cannot find witness for ...; Cannot check relation with uvars
/// The error does not even land on the discard. In the version this fact was extracted
/// from it landed on an assignment to an unrelated local *after* the allocation, because
/// that is the first step that has to look through the unopened existential.
///
/// Three repairs were tried and rejected: binding the witness at the allocation instead
/// of at the discard, discarding the existential slprop directly
/// (`drop_ (exists* m. inv x m)`), and annotating the branch `ensures emp`. The first two
/// fail identically. The third succeeds only when the branch touches nothing else -- add
/// one assignment to an enclosing local and it is `Error 228`, because the annotation is
/// then simply wrong, and computing the right one is the emitter inventing a proof step.
///
/// So the scheme refuses: R4.14a. An object may be allocated in a method's own block, or
/// in a branch that returns; not in a block that closes around it. Below is the shape
/// that works, and it is the one the emitter is allowed to produce.
fn allocate_in_a_returning_branch (b: bool) (capacity: I32.t { I32.v capacity >= 0 })
  requires emp
  returns  n : I32.t
  ensures  pure (I32.v n >= 0)
{
  if b {
    let x = alloc_without_free capacity;
    with m. assert (class_Stack__inv x m);
    drop_ (class_Stack__inv x m);
    capacity
  } else {
    0l
  }
}

/// ---------------------------------------------------------------------------
/// F20. An object's invariant may CONTAIN another object's, and nesting needs no
/// new device: the outer invariant existentially quantifies the sub-object's
/// *model*, exactly as R3.10a quantifies an array's *contents*.
///
///     pair__inv this m =
///       exists* r ml mr.
///         B.pts_to this r **
///         counter__inv r.fld_l ml **      <-- the sub-object, folded
///         counter__inv r.fld_r mr **
///         pure (<clauses over ml and mr> /\ m == <abstraction> ml mr)
///
/// Three consequences, all of them load-bearing, and all of them checked below.
///
///  1. Inside the outer object's unfold window the sub-object is still FOLDED, so
///     calling one of its methods is an ordinary call. The outer window opens the
///     outer box; it does not open what the box holds. This is what makes the
///     nesting compositional rather than merely nested -- an inner class's
///     [Invariant] clauses are proved once, where they were written.
///
///  2. The closing `fold` needs the sub-models, and a method the outer object
///     called may have moved one. So they are named where the fold happens, with
///     F18's idiom used to read rather than to discard. Reusing the binder the
///     `unfold` produced would be wrong: it is stale exactly when it matters.
///
///  3. A bound on a sub-model has to be a REFINEMENT ON THE MODEL TYPE, which is
///     F17 again and is not optional here. `ranked_bump_left` below needs
///     `ml.m_n < 2147483647` to call `counter_bump`. Stating it as a `pure`
///     conjunct inside `counter__inv` does not reach: at the call site the
///     sub-invariant is a folded slprop, so its pure part is not in the context.
///     Removing `counter__model__pred` makes exactly this proof fail, with
///     `Failed to prove pure property: _ml.m_n < 2147483647`.
/// ---------------------------------------------------------------------------

noeq type counter__raw = { fld_k: I32.t }
let counter = B.box counter__raw

noeq type counter__model__raw = { m_n: int }
/// F20.3. The bound lives here, on the type, or it does not reach a caller.
let counter__model__pred (m: counter__model__raw) : prop = 0 <= m.m_n /\ m.m_n <= 2147483647
type counter__model = m: counter__model__raw { counter__model__pred m }

let counter__inv (this: counter) (m: counter__model) : slprop =
  exists* (r: counter__raw).
    B.pts_to this r **
    pure (0 <= I32.v r.fld_k /\ m == { m_n = I32.v r.fld_k })

fn counter_mk (k: I32.t)
  requires pure (0 <= I32.v k)
  returns  c: counter
  ensures  exists* m. counter__inv c m ** pure (m.m_n == I32.v k)
{
  let c = B.alloc ({ fld_k = k });
  fold counter__inv c ({ m_n = I32.v k });
  c
}

fn counter_bump (this: counter) (#pre: erased counter__model)
  requires counter__inv this pre ** pure ((reveal pre).m_n < 2147483647)
  ensures  exists* post. counter__inv this post ** pure (post.m_n == (reveal pre).m_n + 1)
{
  unfold counter__inv this pre;
  let t0 = B.op_Bang this;
  B.op_Colon_Equals this ({ fld_k = I32.add t0.fld_k 1l });
  let t1 = B.op_Bang this;
  fold counter__inv this ({ m_n = I32.v t1.fld_k });
}

noeq type ranked__raw = { fld_l: counter; fld_r: counter }
let ranked = B.box ranked__raw
noeq type ranked__model = { m_l: int; m_r: int }

/// The conjoined invariant: a fact relating two sub-objects, which neither of them
/// could state. This is what composition is for.
let ranked__inv (this: ranked) (m: ranked__model) : slprop =
  exists* (r: ranked__raw) (ml: counter__model) (mr: counter__model).
    B.pts_to this r **
    counter__inv r.fld_l ml **
    counter__inv r.fld_r mr **
    pure (ml.m_n <= mr.m_n /\ m == { m_l = ml.m_n; m_r = mr.m_n })

/// F20, construction: two sub-objects are built folded and handed straight to the
/// composite's fold. Their invariants are consumed, not re-proved.
fn ranked_mk (lo: I32.t) (hi: I32.t)
  requires pure (0 <= I32.v lo /\ I32.v lo <= I32.v hi)
  returns  p: ranked
  ensures  exists* m. ranked__inv p m ** pure (m.m_l == I32.v lo /\ m.m_r == I32.v hi)
{
  let l = counter_mk lo;
  let r = counter_mk hi;
  let p = B.alloc ({ fld_l = l; fld_r = r });
  with ml mr. assert (counter__inv l ml ** counter__inv r mr);
  fold ranked__inv p ({ m_l = ml.m_n; m_r = mr.m_n });
  p
}

/// F20.1 and F20.2 together: an ordinary call on a sub-object inside the outer
/// window, and a fold that names the sub-models where they are, not where they were.
fn ranked_bump_left (this: ranked) (#pre: erased ranked__model)
  requires ranked__inv this pre ** pure ((reveal pre).m_l < (reveal pre).m_r)
  ensures  exists* post. ranked__inv this post **
           pure (post.m_l == (reveal pre).m_l + 1 /\ post.m_r == (reveal pre).m_r)
{
  unfold ranked__inv this pre;
  let t0 = B.op_Bang this;
  counter_bump t0.fld_l;
  with ml' mr'. assert (counter__inv t0.fld_l ml' ** counter__inv t0.fld_r mr');
  fold ranked__inv this ({ m_l = ml'.m_n; m_r = mr'.m_n });
}

// ---------------------------------------------------------------------------
// F21-F25: fractional object invariants (R3.10c, R3.10d)
// ---------------------------------------------------------------------------

/// F21: an slprop `let` may take a **meta-argument-defaulted** permission binder, exactly
///      as `Pulse.Lib.Box.pts_to` does. `frac__inv x m` then *means* `frac__inv x #1.0R m`,
///      so indexing every class invariant by a permission changes no existing emission:
///      full ownership stays the thing you get by not asking for anything.
///
///      The fraction propagates to every resource conjunct -- the box, each array, and
///      each sub-object's own invariant. That is the whole of R3.10c.
noeq type frac__raw = { fld_items: A.array I32.t; fld_top: I32.t }
let frac = B.box frac__raw
noeq type frac__model = { m_elems: Seq.seq I32.t }

let frac__inv (this: frac) (#[T.exact (`1.0R)] p: perm) (m: frac__model) : slprop =
  exists* (r: frac__raw) (contents: Seq.seq I32.t).
    B.pts_to this #p r **
    A.pts_to r.fld_items #p contents **
    pure (Seq.length contents <= 2147483647 /\
          0 <= I32.v r.fld_top /\ I32.v r.fld_top <= Seq.length contents /\
          m == ({ m_elems = Seq.slice contents 0 (I32.v r.fld_top) }))

/// F21, the load-bearing half: the defaulted form and the explicit one are the same
/// slprop. Nothing in R3.10, R4.10 or R4.11 has to change to gain a permission index.
ghost fn frac_default_is_full (this: frac) (#m: frac__model)
  requires frac__inv this m
  ensures  frac__inv this #1.0R m
{ () }

/// F22: the per-class `share` is provable from `Box.share`, `Array.share` and (F23) the
///      sub-objects' own `share`. The `assert` before each `fold` is **required**: the
///      invariant's existentials are solved by matching against the context, and after a
///      share the context holds two candidates for every one of them.
ghost fn frac__inv_share (this: frac) (#p: perm) (#m: frac__model)
  requires frac__inv this #p m
  ensures  frac__inv this #(p /. 2.0R) m ** frac__inv this #(p /. 2.0R) m
{
  unfold (frac__inv this #p m);
  with r. assert (B.pts_to this #p r);
  with contents. assert (A.pts_to r.fld_items #p contents);
  B.share this;
  A.share r.fld_items;
  assert (B.pts_to this #(p /. 2.0R) r ** A.pts_to r.fld_items #(p /. 2.0R) contents);
  fold (frac__inv this #(p /. 2.0R) m);
  assert (B.pts_to this #(p /. 2.0R) r ** A.pts_to r.fld_items #(p /. 2.0R) contents);
  fold (frac__inv this #(p /. 2.0R) m);
}

/// F23: `gather` proves the two models **equal**. It is not an extra hypothesis and not a
///      design choice: R3.9's invariant pins `m` to the abstraction function of the
///      representation, `Box.gather` proves the two representations equal, and a function
///      of equal arguments is equal. So two read-only aliases of one object necessarily
///      agree about it -- which is the entire point of allowing them.
///      The two permissions are **explicit** parameters. As implicits they were solved by
///      matching, and a nested gather could then come back at `q +. p` where its caller
///      wanted `p +. q` -- the same permission, but a user-defined slprop gets no
///      normalisation (F24) and the caller's `fold` is matched syntactically. Naming them
///      at the call site fixes the order once, and the nesting composes.
///
///      The renaming of the second view onto the first happens **before** anything is
///      gathered, via `pts_to_injective_eq` rather than `gather`. `gather` is
///      `allow_ambiguous` and keeps whichever of the two values it matched first, so a
///      later `fold` naming the other one would fail against a resource provably equal to
///      what it wanted. Renaming first leaves exactly one candidate per existential, and
///      then there is nothing left to be ambiguous about.
[@@allow_ambiguous]
ghost fn frac__inv_gather_gen (this: frac) (p q: perm) (#m #m': frac__model)
  requires frac__inv this #p m ** frac__inv this #q m'
  ensures  frac__inv this #(p +. q) m ** pure (m == m')
{
  unfold (frac__inv this #p m);
  with r0. assert (B.pts_to this #p r0);
  with c0. assert (A.pts_to r0.fld_items #p c0);
  unfold (frac__inv this #q m');
  with r1. assert (B.pts_to this #q r1);
  with c1. assert (A.pts_to r1.fld_items #q c1);
  B.pts_to_injective_eq this;
  assert (pure (r0 == r1));
  rewrite (B.pts_to this #q r1) as (B.pts_to this #q r0);
  rewrite (A.pts_to r1.fld_items #q c1) as (A.pts_to r0.fld_items #q c1);
  B.gather this;
  A.gather r0.fld_items;
  fold (frac__inv this #(p +. q) m);
}

/// F24: Pulse normalises `p /. 2.0R +. p /. 2.0R` to `p` for `pts_to`, which has prover
///      support, but **not** for a user-defined slprop, which is matched syntactically.
///      So the emitted `gather` is stated as `share`'s exact inverse and discharges the
///      arithmetic once, here, rather than leaving a `rewrite` at every call site.
[@@allow_ambiguous]
ghost fn frac__inv_gather (this: frac) (#p: perm) (#m #m': frac__model)
  requires frac__inv this #(p /. 2.0R) m ** frac__inv this #(p /. 2.0R) m'
  ensures  frac__inv this #p m ** pure (m == m')
{
  frac__inv_gather_gen this (p /. 2.0R) (p /. 2.0R);
  rewrite (frac__inv this #(p /. 2.0R +. p /. 2.0R) m) as (frac__inv this #p m);
}

/// F23, the nested case: a class owning a class. `share` recurses into the sub-object's
/// own `share`, which is why the lemma is emitted per class rather than written once.
noeq type frac_outer__raw = { fld_inner: frac; fld_n: I32.t }
let frac_outer = B.box frac_outer__raw
noeq type frac_outer__model = { m_inner: frac__model; m_n: int }

let frac_outer__inv (this: frac_outer) (#[T.exact (`1.0R)] p: perm)
                    (m: frac_outer__model) : slprop =
  exists* (r: frac_outer__raw) (model_inner: frac__model).
    B.pts_to this #p r **
    frac__inv r.fld_inner #p model_inner **
    pure (m == ({ m_inner = model_inner; m_n = I32.v r.fld_n }))

ghost fn frac_outer__inv_share (this: frac_outer) (#p: perm) (#m: frac_outer__model)
  requires frac_outer__inv this #p m
  ensures  frac_outer__inv this #(p /. 2.0R) m ** frac_outer__inv this #(p /. 2.0R) m
{
  unfold (frac_outer__inv this #p m);
  with r. assert (B.pts_to this #p r);
  with model_inner. assert (frac__inv r.fld_inner #p model_inner);
  B.share this;
  frac__inv_share r.fld_inner;
  assert (B.pts_to this #(p /. 2.0R) r ** frac__inv r.fld_inner #(p /. 2.0R) model_inner);
  fold (frac_outer__inv this #(p /. 2.0R) m);
  assert (B.pts_to this #(p /. 2.0R) r ** frac__inv r.fld_inner #(p /. 2.0R) model_inner);
  fold (frac_outer__inv this #(p /. 2.0R) m);
}

/// F23, nested `gather`. This is the pin that matters most: with the permissions left
/// implicit, the *outer* fold here failed while every one-level class verified, because
/// only a nested call has a permission for matching to get backwards. A class owning a
/// class is the smallest configuration that can catch it, so it is pinned rather than
/// left to the acceptance suite.
[@@allow_ambiguous]
ghost fn frac_outer__inv_gather_gen (this: frac_outer) (p q: perm)
                                    (#m #alt_m: frac_outer__model)
  requires frac_outer__inv this #p m ** frac_outer__inv this #q alt_m
  ensures  frac_outer__inv this #(p +. q) m ** pure (m == alt_m)
{
  unfold (frac_outer__inv this #p m);
  with r. assert (B.pts_to this #p r);
  with model_inner. assert (frac__inv r.fld_inner #p model_inner);
  unfold (frac_outer__inv this #q alt_m);
  with alt_r. assert (B.pts_to this #q alt_r);
  with alt_model_inner. assert (frac__inv alt_r.fld_inner #q alt_model_inner);
  B.pts_to_injective_eq this;
  assert (pure (r == alt_r));
  rewrite (B.pts_to this #q alt_r) as (B.pts_to this #q r);
  rewrite (frac__inv alt_r.fld_inner #q alt_model_inner)
       as (frac__inv r.fld_inner #q alt_model_inner);
  B.gather this;
  frac__inv_gather_gen r.fld_inner p q;
  fold (frac_outer__inv this #(p +. q) m);
}

[@@allow_ambiguous]
ghost fn frac_outer__inv_gather (this: frac_outer) (#p: perm)
                                (#m #alt_m: frac_outer__model)
  requires frac_outer__inv this #(p /. 2.0R) m ** frac_outer__inv this #(p /. 2.0R) alt_m
  ensures  frac_outer__inv this #p m ** pure (m == alt_m)
{
  frac_outer__inv_gather_gen this (p /. 2.0R) (p /. 2.0R);
  rewrite (frac_outer__inv this #(p /. 2.0R +. p /. 2.0R) m)
       as (frac_outer__inv this #p m);
}

/// An observer: two object parameters at *independent* permissions, which is what makes
/// the two arguments allowed to be the same object.
fn frac_observe (a: frac) (b: frac) (#pa #pb: perm) (#ma #mb: frac__model)
  preserves frac__inv a #pa ma
  preserves frac__inv b #pb mb
  returns v: bool
  ensures pure (v == (Seq.length ma.m_elems = Seq.length mb.m_elems))
{
  unfold (frac__inv a #pa ma);
  let ra = !a;
  fold (frac__inv a #pa ma);
  unfold (frac__inv b #pb mb);
  let rb = !b;
  fold (frac__inv b #pb mb);
  (I32.v ra.fld_top = I32.v rb.fld_top)
}

/// F25: Pulse does **not** split a permission at a call site. Dropping the `share` below
///      fails with `Cannot prove: frac__inv s _` against a context holding exactly
///      `frac__inv s m`, because splitting is a proof step and Pulse does not guess it.
///      So read-only aliasing is reached by asking for it, in C#, with `Pal.Share`.
///
///      The same is true of an array: `f a a` with two `[Frac]` parameters needs
///      `A.share a` first (`frac_alias_array`). R4.9 has claimed since M1 that "the same
///      array may be passed to two parameters at once"; until now nothing tested it, and
///      it was not in fact reachable.
fn frac_alias (s: frac) (#m: frac__model)
  preserves frac__inv s m
  returns v: bool
{
  frac__inv_share s;
  let v = frac_observe s s;
  frac__inv_gather s;
  v
}

fn frac_observe_array (a: A.array I32.t) (b: A.array I32.t) (#pa #pb: perm)
                      (#sa #sb: erased (Seq.seq I32.t))
  preserves A.pts_to a #pa sa
  preserves A.pts_to b #pb sb
  returns v: bool
{ true }

fn frac_alias_array (a: A.array I32.t) (#s: erased (Seq.seq I32.t))
  preserves A.pts_to a s
  returns v: bool
{
  A.share a;
  let v = frac_observe_array a a;
  A.gather a;
  v
}

/// F26: generalising a **read-only** method over the permission is a *pure* generalisation.
///      A caller holding full ownership calls it with nothing written and nothing changed,
///      because Pulse instantiates the binder at `1.0R`. So R4.11's existing write-set
///      analysis -- which already decides `preserves` -- decides this too, and read-only
///      aliasing costs no annotation on any instance method.
///
///      It is also *necessary* for composition, not merely convenient. R3.10c propagates
///      the outer fraction into a sub-object's invariant, so a read-only method of an
///      owner holds `class_D__inv r.fld_g #p model_g` and can only call `D`'s readers if
///      they too are generalised. A scheme that fixed sub-readers at `1.0R` would make
///      every fractional owner unable to read its own parts.
fn frac_peek (this: frac) (#p: perm) (#m: erased frac__model)
  preserves frac__inv this #p m
  returns v: I32.t
  ensures pure (I32.v v == Seq.length (reveal m).m_elems)
{
  unfold (frac__inv this #p m);
  let r = !this;
  fold (frac__inv this #p m);
  r.fld_top
}

fn frac_full_owner_reads (this: frac) (#m: erased frac__model)
  preserves frac__inv this m
  returns v: I32.t
{
  frac_peek this
}

/// The composition half: an owner at permission `p` reading through its sub-object.
fn frac_outer_peek (this: frac_outer) (#p: perm) (#m: erased frac_outer__model)
  preserves frac_outer__inv this #p m
  returns v: I32.t
{
  unfold (frac_outer__inv this #p m);
  let r = !this;
  let v = frac_peek r.fld_inner;
  with mi. assert (frac__inv r.fld_inner #p mi);
  fold (frac_outer__inv this #p m);
  v
}

/// F27: **two** views of one object may be in scope at once; **three** may not. Matching an
///      slprop against the context is a search for a unique candidate, and after a second
///      `share` there are three resources with the same head and the same name, so the
///      match is ambiguous and the call is refused -- `Cannot prove: frac__inv s _`
///      against a context listing the very thing it wants, three times over.
///
///      Two is enough for the feature, which is read-only aliasing between two names, and
///      more than two is reached by *nesting*: share, use both halves, gather, and only
///      then share again. What is not available is holding three views simultaneously.
///      This is a fact about Pulse's matcher and not about permissions -- splitting is
///      unbounded, as `frac_split_thrice` shows -- so it is pinned rather than designed
///      around.
fn frac_two_views (s: frac) (#m: frac__model)
  preserves frac__inv s m
  returns v: I32.t
{
  frac__inv_share s;
  let v = frac_peek s;
  frac__inv_gather s;
  v
}

[@@expect_failure]
fn frac_three_views (s: frac) (#m: frac__model)
  preserves frac__inv s m
  returns v: I32.t
{
  frac__inv_share s;
  frac__inv_share s;
  let v = frac_peek s;
  frac__inv_gather s;
  frac__inv_gather s;
  v
}

/// The permission itself splits as far as anyone likes; it is only *simultaneous* views
/// that are limited. Halving twice and recombining twice is fine as long as no third view
/// is live at the point of a call.
ghost fn frac_split_thrice (s: frac) (#m: frac__model)
  preserves frac__inv s m
{
  frac__inv_share s;
  frac__inv_share s;
  frac__inv_gather s;
  frac__inv_gather s;
}
