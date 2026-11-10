module SpanLengthFalse
#lang-pulse
open Pulse
open Pulse.Lib.CSharp.Assumptions
module V = Pulse.Lib.Vec
module S = Pulse.Lib.Slice
module CS = Pulse.Lib.CSharp.Span

// This verified before the span length refinement. Never execute it.
fn contradiction ()
  requires emp
  ensures pure False
{
  let n = FStar.SizeT.uint32_to_sizet 2147483648ul;
  let v = V.alloc () n;
  let a = V.vec_to_array v;
  V.to_array_pts_to v;
  rewrite each (V.vec_to_array v) as a;
  let s = S.from_array a n;
  CS.span_length_bound s;
  ()
}
