module PlainLocals
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module C = Class_OwnedCell
module I = FStar.Int32

#set-options "--z3rlimit 5"

let snapshot (value: FStar.Int.int_t I.n) : C.class_OwnedCell__raw =
  { C.fld_value = I.int_to_t value }

ghost fn canonical (c: C.class_OwnedCell) (value: I.t)
  requires OwnerCells.held c (I.v value)
  ensures OwnerCells.raw c (snapshot (I.v value)) 1.0R
{
  unfold (OwnerCells.held c (I.v value));
  with x. _;
  I.v_inj x value;
  I.v_inj value (I.int_to_t (I.v value));
}

// This predicate is well-typed for nullable backing storage, but actual
// ownership proves the reference is non-null; null supplies no fake cell.
unfold let held (c: C.class_OwnedCell__opt) (value: int) =
  exists* (x: I.t). B.pts_to c { C.fld_value = x } ** pure (I.v x == value)

ghost fn assigned (c: C.class_OwnedCell__opt) (value: int)
  preserves held c value
  ensures pure (c =!= B.null)
{
  unfold (held c value);
  with x. _;
  B.pts_to_not_null c;
}
