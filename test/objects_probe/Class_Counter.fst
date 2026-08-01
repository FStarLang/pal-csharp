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

(* R3.10: the invariant, indexed by the model.  The model type here is `SpecInt`, so
   `int`; no model type declaration is emitted.  The conjuncts are, in order: the
   [Invariant] clauses, then the abstraction relation from the [Model] member's body. *)
let class_Counter__inv (this: class_Counter) (m: int) : slprop =
  exists* (r: class_Counter__raw).
    B.pts_to this r **
    pure (((I32.v r.fld_count) >= 0) /\
          (m == (I32.v r.fld_count)))

(* R3.9c: each [Spec] member is a pure function of the model. *)
let spec_Counter_Value (m: int) : int = m
