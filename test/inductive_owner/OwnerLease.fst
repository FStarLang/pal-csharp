module OwnerLease
#lang-pulse
open Pulse.Lib.Pervasives
module C = Class_CellOwner
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

unfold let inv (owner: C.class_CellOwner) (value: int) (p: perm) =
  C.class_CellOwner__inv owner #p value

let opened (owner: C.class_CellOwner) (value: int) (p: perm) =
  exists* r.
    B.pts_to owner #p r **
    OwnerCells.holds r.C.fld_cell value p **
    pure (value == OwnerState.value r.C.fld_state)

ghost fn begin_read (owner: C.class_CellOwner) (value: int) (p: perm)
  requires inv owner value p
  ensures opened owner value p
{
  unfold (inv owner value p);
  unfold (C.class_CellOwner__inv owner #p value);
  with r. _;
  rewrite (OwnerCells.holds r.C.fld_cell (OwnerState.value r.C.fld_state) p)
    as (OwnerCells.holds r.C.fld_cell value p);
  fold (opened owner value p);
}

ghost fn end_read (owner: C.class_CellOwner) (value: int) (p: perm)
  requires opened owner value p
  ensures inv owner value p
{
  unfold (opened owner value p);
  with r. _;
  rewrite (OwnerCells.holds r.C.fld_cell value p)
    as (OwnerCells.holds r.C.fld_cell (OwnerState.value r.C.fld_state) p);
  fold (C.class_CellOwner__inv owner #p value);
  fold (inv owner value p);
}
