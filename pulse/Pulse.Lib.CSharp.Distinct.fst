module Pulse.Lib.CSharp.Distinct
#lang-pulse

/// R27.50. Two objects whose invariants are held at once, each whole, are two objects:
/// a box owned twice at full permission would be owned at permission 2.

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference

ghost
fn same_box_false (#a: Type0) (x: B.box a) (#v #w: a)
  requires B.pts_to x v
  requires B.pts_to x w
  ensures pure False
{
  B.gather x #v #w;
  B.to_ref_pts_to x;
  R.pts_to_perm_bound (B.box_to_ref x);
  unreachable ()
}

ghost
fn boxes_distinct (#a: Type0) (x y: B.box a) (#v #w: a)
  preserves B.pts_to x v
  preserves B.pts_to y w
  ensures pure (~(x == y))
{
  let b = FStar.IndefiniteDescription.strong_excluded_middle (x == y);
  if b {
    rewrite (B.pts_to y w) as (B.pts_to x w);
    same_box_false x #v #w;
    unreachable ()
  } else {
    ()
  }
}
