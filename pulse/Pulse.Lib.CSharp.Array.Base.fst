module Pulse.Lib.CSharp.Array.Base
#lang-pulse

open Pulse
module Raw = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module I32 = FStar.Int32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module T = FStar.Tactics.V2

noeq type array (t: Type0) = {
  raw_count: (n: I32.t { I32.v n >= 0 });
  raw_storage: (a: Raw.array t {
    (Raw.is_null a ==> I32.v raw_count == 0) /\
    (not (Raw.is_null a) ==> Raw.length a == I32.v raw_count)
  })
}

let count (#t: Type0) (a: array t) = a.raw_count
let storage (#t: Type0) (a: array t) = a.raw_storage
let null (#t: Type0) : array t = { raw_count = 0l; raw_storage = Raw.null }

let pts_to (#t: Type0) ([@@@mkey] a: array t)
  (#[T.exact (`1.0R)] p: perm) (s: Seq.seq t) : slprop =
  Raw.pts_to (storage a) #p s

ghost
fn to_raw (#t: Type0) (a: array t) (#p: perm) (#s: Ghost.erased (Seq.seq t))
  requires pts_to a #p s
  ensures Raw.pts_to (storage a) #p s
{
  unfold (pts_to a #p s)
}

ghost
fn of_raw (#t: Type0) (a: array t) (#p: perm) (#s: Ghost.erased (Seq.seq t))
  requires Raw.pts_to (storage a) #p s
  ensures pts_to a #p s
{
  fold (pts_to a #p s)
}

ghost
fn pts_to_len (#t: Type0) (a: array t) (#p: perm) (#s: Seq.seq t)
  preserves pts_to a #p s
  ensures pure (length a == Seq.length s)
{
  to_raw a;
  Raw.pts_to_not_null (storage a);
  Raw.pts_to_len (storage a);
  of_raw a
}

ghost
fn pts_to_not_null (#t: Type0) (#p: perm) (a: array t) (#s: Seq.seq t)
  preserves pts_to a #p s
  ensures pure (not (is_null a))
{
  to_raw a;
  Raw.pts_to_not_null (storage a);
  of_raw a
}

ghost
fn pts_to_perm_bound (#t: Type0) (a: array t) (#p: perm) (#s: Seq.seq t)
  preserves pts_to a #p s
  requires pure (Seq.length s > 0)
  ensures pure (p <=. 1.0R)
{
  to_raw a;
  Raw.pts_to_perm_bound (storage a);
  of_raw a
}

ghost
fn share (#t: Type0) (a: array t) (#s: Ghost.erased (Seq.seq t)) (#p: perm)
  requires pts_to a #p s
  ensures pts_to a #(p /. 2.0R) s ** pts_to a #(p /. 2.0R) s
{
  to_raw a;
  Raw.share (storage a);
  of_raw a;
  of_raw a
}

[@@allow_ambiguous]
ghost
fn gather (#t: Type0) (a: array t)
  (#s0 #s1: Ghost.erased (Seq.seq t)) (#p0 #p1: perm)
  requires pts_to a #p0 s0 ** pts_to a #p1 s1
  ensures pts_to a #(p0 +. p1) s0 ** pure (s0 == s1)
{
  to_raw a #p0 #s0;
  to_raw a #p1 #s1;
  Raw.gather (storage a) #s0 #s1 #p0 #p1;
  of_raw a
}

fn ( .() ) (#t: Type0) (a: array t) (i: SZ.t) (#p: perm)
  (#s: Ghost.erased (Seq.seq t) { SZ.v i < Seq.length s })
  preserves pts_to a #p s
  returns x: t
  ensures rewrites_to x (Seq.index s (SZ.v i))
{
  to_raw a;
  let x = Raw.op_Dot_Lparen_Rparen (storage a) i;
  of_raw a;
  x
}

fn ( .()<- ) (#t: Type0) (a: array t) (i: SZ.t) (x: t)
  (#s: Ghost.erased (Seq.seq t) { SZ.v i < Seq.length s })
  requires pts_to a s
  ensures pts_to a (Seq.upd s (SZ.v i) x)
{
  to_raw a;
  Raw.op_Dot_Lparen_Rparen_Less_Minus (storage a) i x;
  of_raw a
}

fn alloc (#t: Type0) (n: I32.t { I32.v n >= 0 }) (init: t)
  requires emp
  returns a: array t
  ensures pts_to a (Seq.create (I32.v n) init)
{
  let v = V.alloc init (Pulse.Lib.CSharp.Casts.idx n);
  let raw = V.vec_to_array v;
  V.to_array_pts_to v;
  rewrite each (V.vec_to_array v) as raw;
  Raw.pts_to_not_null raw;
  let a: array t = { raw_count = n; raw_storage = raw };
  rewrite each raw as (storage a);
  of_raw a;
  a
}

fn memcpy_l (#t: Type0) (n: SZ.t)
  (src dst: (a:array t { SZ.v n <= length a }))
  (#p: perm) (#s #d: Ghost.erased (Seq.seq t))
  requires pts_to src #p s ** pts_to dst d
  returns squash (Seq.length s == length src /\ Seq.length d == length dst)
  ensures pts_to src #p s **
    pts_to dst (Seq.append (Seq.slice s 0 (SZ.v n))
                          (Seq.slice d (SZ.v n) (length dst)))
{
  pts_to_len src;
  pts_to_len dst;
  to_raw src;
  to_raw dst;
  Raw.pts_to_len (storage src);
  Raw.pts_to_len (storage dst);
  let r = Raw.memcpy_l n (storage src) (storage dst);
  of_raw src;
  of_raw dst;
  r
}
