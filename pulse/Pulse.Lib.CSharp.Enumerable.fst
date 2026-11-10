module Pulse.Lib.CSharp.Enumerable
#lang-pulse

open Pulse
open Pulse.Lib.CSharp.Casts
module A = Pulse.Lib.CSharp.Array.Base
module CA = Pulse.Lib.CSharp.Array
module R = Pulse.Lib.Reference
module I32 = FStar.Int32
module Seq = FStar.Seq
module CS = Pulse.Lib.CSharp.Seq

noeq type enumerable (t: Type0) = { items: A.array t; coll: bool }

let pts_to (#t: Type0) ([@@@mkey] e: enumerable t) (#p: perm) (s: Seq.seq t) : slprop =
  A.pts_to e.items #p s

ghost
fn pts_to_len (#t: Type0) (e: enumerable t) (#p: perm) (#s: Seq.seq t)
  preserves pts_to e #p s
  ensures pure (Seq.length s < pow2 31)
{
  unfold (pts_to e #p s);
  A.pts_to_len e.items;
  fold (pts_to e #p s);
}

let is_collection (#t: Type0) (e: enumerable t) : bool = e.coll

fn count (#t: Type0) (e: enumerable t { is_collection e })
  (#p: perm) (#s: Ghost.erased (Seq.seq t))
  preserves pts_to e #p s
  returns n: I32.t
  ensures pure (I32.v n == Seq.length s)
{
  unfold (pts_to e #p s);
  let n = CA.length_i32 e.items;
  fold (pts_to e #p s);
  n
}

fn copy_to (#t: Type0) (e: enumerable t { is_collection e }) (dst: A.array t) (i: I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq t))
  (#d: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i + Seq.length s <= Seq.length d })
  preserves pts_to e #p s
  requires A.pts_to dst d
  ensures A.pts_to dst (CS.copied_at s 0 d (I32.v i) (Seq.length s))
{
  unfold (pts_to e #p s);
  let n = CA.length_i32 e.items;
  CA.copy_at e.items 0l dst i n;
  fold (pts_to e #p s);
}

fn move_next (#t: Type0) (e: enumerable t) (r: R.ref I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq t)) (#k: Ghost.erased I32.t)
  preserves pts_to e #p s
  requires R.pts_to r k
  returns b: bool
  ensures R.pts_to r (advance s k) ** pure (b == (I32.v k < Seq.length s) /\ Seq.length s < pow2 31)
{
  unfold (pts_to e #p s);
  let n = CA.length_i32 e.items;
  fold (pts_to e #p s);
  let vk = !r;
  if (I32.lt vk n) {
    r := I32.add vk 1l;
    true
  } else {
    false
  }
}

fn current (#t: Type0) (e: enumerable t) (r: R.ref I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq t))
  (#k: Ghost.erased I32.t { 1 <= I32.v k /\ I32.v k <= Seq.length s })
  preserves pts_to e #p s ** R.pts_to r k
  returns x: t
  ensures rewrites_to x (Seq.index s (I32.v k - 1))
{
  unfold (pts_to e #p s);
  let vk = !r;
  let x = CA.read e.items (I32.sub vk 1l);
  fold (pts_to e #p s);
  x
}

let view (#t: Type0) (a: A.array t) (coll: bool) : e: enumerable t { is_collection e == coll } =
  { items = a; coll }

ghost
fn lend (#t: Type0) (a: A.array t) (coll: bool) (#p: perm) (#s: Seq.seq t)
  requires A.pts_to a #p s
  ensures pts_to (view a coll) #p s
{
  rewrite (A.pts_to a #p s) as (A.pts_to (view a coll).items #p s);
  fold (pts_to (view a coll) #p s);
}

ghost
fn unlend (#t: Type0) (a: A.array t) (coll: bool) (#p: perm) (#s: Seq.seq t)
  requires pts_to (view a coll) #p s
  ensures A.pts_to a #p s
{
  unfold (pts_to (view a coll) #p s);
  rewrite (A.pts_to (view a coll).items #p s) as (A.pts_to a #p s);
}
