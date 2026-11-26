module ProjectedFacts
#lang-pulse
open Pulse
module C = Pulse.Lib.CSharp.Enumerable.Cast
module S = Pulse.Lib.CSharp.Enumerable.Source
module B = Pulse.Lib.Box
module A = Pulse.Lib.CSharp.Array.Base
module I32 = FStar.Int32
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

type state = I32.t & I32.t
let before : state = (7l, 5l)
let after : state = (7l, 9l)
let project (m: state) = Seq.create 1 (fst m)
let owns (b: B.box state) (p: perm) (m: state) = B.pts_to b #p m
let misses (_: FStar.Dyn.dyn) (_: perm) (_: Seq.seq I32.t) = emp

// This write has full permission and verifies independently. Thus the negative
// test below is about lost model information, not insufficient write permission.
fn change_hidden (b: B.box state)
  requires owns b 1.0R before
  ensures owns b 1.0R after
{
  unfold (owns b 1.0R before);
  B.op_Colon_Equals b after;
  fold (owns b 1.0R after);
}

[@@expect_failure]
fn cannot_restore_changed_hidden_state (b: B.box state) (a: A.array I32.t)
  requires owns b 1.0R before ** A.pts_to a (project before)
  ensures S.pts_to (C.resource owns project misses) C.contents
    (C.matching b (hide before) a false) 1.0R (hide (project before))
{
  C.lend_match owns project misses b (hide before) a false;
  let e = C.matching b (hide before) a false;
  rewrite each (C.matching b (hide before) a false) as e;
  let x = C.open_match owns project misses e;
  rewrite (owns x 1.0R (reveal (C.model e))) as (owns x 1.0R before);
  change_hidden x;
  assert pure (Seq.equal (project before) (project after));
  C.close_match owns project misses e x;
}
