module ArrayLengthFalse
#lang-pulse
open Pulse
open Pulse.Lib.CSharp.Assumptions
module V = Pulse.Lib.Vec
module CA = Pulse.Lib.CSharp.Array

// This verified before the length-carrying representation. Never execute it.
fn contradiction ()
  requires emp
  ensures pure False
{
  let n = FStar.SizeT.uint32_to_sizet 2147483648ul;
  let v = V.alloc () n;
  let a = V.vec_to_array v;
  CA.arr_length_bound a;
  ()
}
