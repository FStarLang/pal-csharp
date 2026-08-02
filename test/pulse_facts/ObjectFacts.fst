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

module A = Pulse.Lib.Array
module B = Pulse.Lib.Box
open Pulse.Lib.Box { box, (!), (:=) }
module CA = Pulse.Lib.CSharp.Array
module I32 = FStar.Int32
module Seq = FStar.Seq

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
