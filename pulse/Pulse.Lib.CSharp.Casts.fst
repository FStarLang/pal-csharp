module Pulse.Lib.CSharp.Casts

open Pulse.Lib.CSharp.Assumptions

module C = FStar.Int.Cast
module I32 = FStar.Int32
module SZ = FStar.SizeT

let int32_to_sizet (x: I32.t) =
  SZ.uint32_to_sizet (C.int32_to_uint32 x)

let sizet_to_int32 (x: SZ.t) =
  C.uint32_to_int32 (SZ.sizet_to_uint32 x)
