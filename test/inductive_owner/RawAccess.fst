module RawAccess

module C = Class_RawOwner
module B = Pulse.Lib.Box
module H = RetainedOwner
module I32 = FStar.Int32

unfold let raw (owner: B.box (C.class_RawOwner__raw)) (r: C.class_RawOwner__raw)
    (p: PulseCore.FractionalPermission.perm) = B.pts_to owner #p r
let value (r: C.class_RawOwner__raw) = I32.v r.C.fld_value
let with_value (r: C.class_RawOwner__raw) (v: int{I32.fits v}) =
  { r with C.fld_value=I32.int_to_t v }
let with_state (r: C.class_RawOwner__raw) (payload: H.payload) =
  { r with C.fld_state=H.of_payload payload }
let half : PulseCore.FractionalPermission.perm = 0.5R
