module CallbackCells

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module C = Class_CallbackCell

unfold let raw (#t: Type0) (cell: C.class_CallbackCell t)
    (snapshot: C.class_CallbackCell__raw t) (permission: perm) : slprop =
  B.pts_to cell #permission snapshot

let value (#t: Type0) (snapshot: C.class_CallbackCell__raw t) : t =
  snapshot.C.fld_item

let int_value (snapshot: C.class_CallbackCell__raw FStar.Int32.t) : int =
  FStar.Int32.v (value snapshot)
