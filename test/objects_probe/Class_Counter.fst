module Class_Counter
#lang-pulse

open Pulse

module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module Seq = FStar.Seq

(* R3.7: the representation -- the class's fields, `fld_`-prefixed as for a struct. *)
noeq type class_Counter__raw = {
  fld_count: I32.t;
}

(* R3.8: the object reference type. *)
let class_Counter = B.box class_Counter__raw

(* R3.9d: the **refined model type**, emitted per class and named `class_C__model`.
   Its shape is R3.5's verbatim -- a predicate plus a refined abbreviation -- and it is
   emitted unconditionally, with the predicate `True` when there are no [Refine] clauses,
   for the same reason `struct_S__pred` is (§0 rule 2).

   Naming it after the *class* rather than after the model type is what lets an atomic
   model such as `SpecInt` carry a refinement at all: there is no user-declared struct to
   put one on, and two classes modelled by `SpecInt` must not collide.

   This is where a fact about the model alone must live. Placed in the invariant below it
   would be true and unreachable, because a caller holds the invariant opaquely (F17). *)
let class_Counter__model__pred (m: int) : prop = m >= 0
type class_Counter__model = m: int { class_Counter__model__pred m }

(* R3.10: the invariant, indexed by the model.  The model type here is `SpecInt`, so
   `int`; no model type declaration is emitted.  The conjuncts are, in order: the
   [Invariant] clauses, then the abstraction relation from the [Model] member's body. *)
let class_Counter__inv (this: class_Counter) (m: class_Counter__model) : slprop =
  exists* (r: class_Counter__raw).
    B.pts_to this r **
    pure (((I32.v r.fld_count) >= 0) /\
          (m == (I32.v r.fld_count)))

(* R3.9c: each [Spec] member is a pure function of the model. *)
let spec_Counter_Value (m: class_Counter__model) : int = m
