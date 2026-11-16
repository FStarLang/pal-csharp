module OwnerCells
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module C = Class_OwnedCell
module I = FStar.Int32
module F = Pulse.Lib.CSharp.Ownership

unfold let raw (c: C.class_OwnedCell) (v: C.class_OwnedCell__raw) (p: perm) : slprop =
  B.pts_to c #p v

let raw_value (v: C.class_OwnedCell__raw) = I.v v.C.fld_value

unfold let held (c: C.class_OwnedCell) (v: int) : slprop =
  exists* (x: I.t). B.pts_to c { C.fld_value = x } ** pure (I.v x == v)

unfold let cell (c: C.class_OwnedCell) : slprop =
  exists* (x: I.t). B.pts_to c { C.fld_value = x }

let holds (c: C.class_OwnedCell) (v: int) (p: perm) : slprop =
  exists* (x: I.t). B.pts_to c #p { C.fld_value = x } ** pure (I.v x == v)

unfold let opened (c: C.class_OwnedCell) (v: int) (p: perm) : slprop =
  exists* (x: I.t). B.pts_to c #p { C.fld_value = x } ** pure (I.v x == v)

ghost fn close (c: C.class_OwnedCell) (v: I.t)
  requires held c (I.v v)
  ensures holds c (I.v v) 1.0R
{
  fold (holds c (I.v v) 1.0R);
}

ghost fn open_cell (c: C.class_OwnedCell) (v: I.t)
  requires holds c (I.v v) 1.0R
  ensures B.pts_to c ({ C.fld_value = v })
{
  unfold (holds c (I.v v) 1.0R);
  with x. assert (B.pts_to c { C.fld_value = x });
  I.v_inj x v;
}

ghost fn open_state (c: C.class_OwnedCell) (s: OwnerState.state) (p: perm)
  requires holds c (OwnerState.value s) p
  ensures opened c (OwnerState.value s) p
{
  unfold (holds c (OwnerState.value s) p);
}

ghost fn close_state (c: C.class_OwnedCell) (s: OwnerState.state) (p: perm)
  requires opened c (OwnerState.value s) p
  ensures holds c (OwnerState.value s) p
{
  fold (holds c (OwnerState.value s) p);
}

ghost fn share (c: C.class_OwnedCell) (v: int) (p: perm) ()
  requires holds c v p
  ensures holds c v (p /. 2.0R) ** holds c v (p /. 2.0R)
{
  unfold (holds c v p);
  B.share c;
  fold (holds c v (p /. 2.0R));
  fold (holds c v (p /. 2.0R));
}

ghost fn gather (c: C.class_OwnedCell) (v: int) (p q: perm) ()
  requires holds c v p ** holds c v q
  ensures holds c v (p +. q)
{
  unfold (holds c v p);
  unfold (holds c v q);
  B.gather c;
  fold (holds c v (p +. q));
}

instance fractional_holds (c: C.class_OwnedCell) (v: int)
  : F.fractional (fun p -> holds c v p) =
  F.Mkfractional #(fun p -> holds c v p)
    (fun p () -> share c v p ())
    (fun p q () -> gather c v p q ())
