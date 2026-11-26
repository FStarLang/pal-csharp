module GhostStoragePlain
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module C = Class_GhostStoragePlain

unfold let zero (o: C.class_GhostStoragePlain) : slprop =
  exists* (r: C.class_GhostStoragePlain__raw).
    B.pts_to o r ** pure (OwnerState.value r.C.fld_State == 0)
