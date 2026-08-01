module Smoke

/// Toolchain smoke test.
///
/// This is NOT a translation target and NOT a golden file. Its only job is
/// to prove that `tools/run-fstar.sh` can typecheck a Pulse program with a
/// mutable-reference contract, so that a broken toolchain is distinguishable
/// from a broken translator.

open Pulse
module R = Pulse.Lib.Reference
#lang-pulse

fn swap (x: R.ref int) (y: R.ref int) (#vx #vy: erased int)
requires R.pts_to x vx ** R.pts_to y vy
ensures R.pts_to x vy ** R.pts_to y vx
{
  let tmp = !y;
  let vx' = !x;
  x := tmp;
  y := vx';
}
