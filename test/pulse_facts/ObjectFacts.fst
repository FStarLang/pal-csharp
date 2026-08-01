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

/// R3.9: the **model** of the object. The critical design constraint is that the model
/// must expose every observation a *caller* needs in order to establish a precondition
/// or exploit a postcondition. A bare `Seq.seq I32.t` would be too weak: a client could
/// not state "the stack is not full", because capacity would be hidden inside the
/// invariant's existential. So the model is a record of exactly the `[Spec]`-visible
/// observations of the class.
noeq type class_Stack__model = { elems: Seq.seq I32.t; cap: nat }

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
let class_Stack__inv (this: class_Stack) (m: class_Stack__model) : slprop =
  exists* (r: class_Stack__raw) (contents: Seq.seq I32.t).
    B.pts_to this r **
    A.pts_to r.fld_items contents **
    pure (I32.v r.fld_top == Seq.length m.elems /\
          Seq.length contents == m.cap /\
          Seq.length m.elems <= m.cap /\
          m.cap <= 2147483647 /\
          m.elems `Seq.equal` Seq.slice contents 0 (Seq.length m.elems))

/// F13: `preserves p` is a real `fn` spec clause in the pinned toolchain, and it composes
///      with `requires`/`ensures`. It is exactly `requires p ensures p`, so it is the
///      right -- and cheapest -- form for a **read-only** method, and *only* for one: on a
///      mutating method `preserves inv this` would be true but vacuous.
fn count (this: class_Stack) (#m: erased class_Stack__model)
  preserves class_Stack__inv this m
  returns  n : I32.t
  ensures  pure (I32.v n == Seq.length (reveal m).elems)
{
  unfold class_Stack__inv this m;
  let r = !this;
  fold class_Stack__inv this m;
  r.fld_top
}

/// R4.10: a mutating method threads the model through. The postcondition names the
/// *new* model as a pure function of the old one, which is what a caller needs; the
/// precondition may mention the old model, which is how "not full" becomes statable.
fn push (this: class_Stack) (v: I32.t) (#m: erased class_Stack__model)
  requires class_Stack__inv this m ** pure (Seq.length (reveal m).elems < (reveal m).cap)
  ensures  class_Stack__inv this
             ({ elems = Seq.snoc (reveal m).elems v; cap = (reveal m).cap })
{
  unfold class_Stack__inv this m;
  let r = !this;
  CA.write r.fld_items r.fld_top v;
  this := { r with fld_top = I32.add r.fld_top 1l };
  fold class_Stack__inv this ({ elems = Seq.snoc (reveal m).elems v; cap = (reveal m).cap });
}

/// R4.11 and F15: a constructor allocates, establishes the invariant, and returns the
/// object. Nothing frees either the array or the box; the function is accepted anyway,
/// which is the whole content of F15. Freshness is *free*: the frame rule gives every
/// caller `frame ** inv x m0`, so a newly constructed object is automatically separate
/// from everything that already existed. No emitter work is needed for that.
fn alloc_without_free (capacity: I32.t { I32.v capacity >= 0 })
  requires emp
  returns  x : class_Stack
  ensures  class_Stack__inv x ({ elems = Seq.empty; cap = I32.v capacity })
{
  let items = CA.alloc capacity 0l;
  let x = B.alloc ({ fld_items = items; fld_top = 0l });
  fold class_Stack__inv x ({ elems = Seq.empty; cap = I32.v capacity });
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
fn merge (a: class_Stack) (b: class_Stack) (#ma #mb: erased class_Stack__model)
  preserves class_Stack__inv a ma
  preserves class_Stack__inv b mb
{
  ()
}

fn aliasing_is_unprovable (a: class_Stack) (#ma: erased class_Stack__model)
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
fn ownership_implies_non_null (this: class_Stack) (#m: erased class_Stack__model)
  preserves class_Stack__inv this m
  ensures  pure (not (B.is_null this))
{
  unfold class_Stack__inv this m;
  B.pts_to_not_null this;
  fold class_Stack__inv this m;
}
