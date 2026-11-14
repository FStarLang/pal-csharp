module RawShared
module C = Class_RawGeneric
module B = Pulse.Lib.Box

unfold let raw (#a #b: Type0) (owner: C.class_RawGeneric a b)
    (r: C.class_RawGeneric__raw a b) (p: PulseCore.FractionalPermission.perm) =
  B.pts_to owner #p r
let value (#a #b: Type0) (r: C.class_RawGeneric__raw a b) = r.C.fld_value
let with_value (#a #b: Type0) (r: C.class_RawGeneric__raw a b) (v: a) =
  { r with C.fld_value=v }
