module Pulse.Lib.CSharp.Array.Base
#lang-pulse

open Pulse
module Raw = Pulse.Lib.Array
module I32 = FStar.Int32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module T = FStar.Tactics.V2

noeq type array (t: Type0) = {
  count: (n: I32.t { I32.v n >= 0 });
  storage: (a: Raw.array t {
    (Raw.is_null a ==> I32.v count == 0) /\
    (not (Raw.is_null a) ==> Raw.length a == I32.v count)
  })
}

let length (#t: Type0) (a: array t) : nat = I32.v a.count
let null (#t: Type0) : array t = { count = 0l; storage = Raw.null }
let is_null (#t: Type0) (a: array t) : bool = Raw.is_null a.storage

val pts_to (#t: Type0) ([@@@mkey] a: array t)
  (#[T.exact (`1.0R)] p: perm) (s: Seq.seq t) : slprop

[@@pulse_unfold]
instance has_pts_to_array (t: Type0) : Pulse.Class.PtsTo.has_pts_to (array t) (Seq.seq t) = {
  pts_to = pts_to
}

ghost
fn to_raw (#t: Type0) (a: array t) (#p: perm) (#s: Ghost.erased (Seq.seq t))
  requires pts_to a #p s
  ensures Raw.pts_to a.storage #p s

ghost
fn of_raw (#t: Type0) (a: array t) (#p: perm) (#s: Ghost.erased (Seq.seq t))
  requires Raw.pts_to a.storage #p s
  ensures pts_to a #p s

ghost
fn pts_to_len (#t: Type0) (a: array t) (#p: perm) (#s: Seq.seq t)
  preserves pts_to a #p s
  ensures pure (length a == Seq.length s)

ghost
fn pts_to_not_null (#t: Type0) (#p: perm) (a: array t) (#s: Seq.seq t)
  preserves pts_to a #p s
  ensures pure (not (is_null a))

ghost
fn pts_to_perm_bound (#t: Type0) (a: array t) (#p: perm) (#s: Seq.seq t)
  preserves pts_to a #p s
  requires pure (Seq.length s > 0)
  ensures pure (p <=. 1.0R)

ghost
fn share (#t: Type0) (a: array t) (#s: Ghost.erased (Seq.seq t)) (#p: perm)
  requires pts_to a #p s
  ensures pts_to a #(p /. 2.0R) s ** pts_to a #(p /. 2.0R) s

[@@allow_ambiguous]
ghost
fn gather (#t: Type0) (a: array t)
  (#s0 #s1: Ghost.erased (Seq.seq t)) (#p0 #p1: perm)
  requires pts_to a #p0 s0 ** pts_to a #p1 s1
  ensures pts_to a #(p0 +. p1) s0 ** pure (s0 == s1)

fn ( .() ) (#t: Type0) (a: array t) (i: SZ.t) (#p: perm)
  (#s: Ghost.erased (Seq.seq t) { SZ.v i < Seq.length s })
  preserves pts_to a #p s
  returns x: t
  ensures rewrites_to x (Seq.index s (SZ.v i))

fn ( .()<- ) (#t: Type0) (a: array t) (i: SZ.t) (x: t)
  (#s: Ghost.erased (Seq.seq t) { SZ.v i < Seq.length s })
  requires pts_to a s
  ensures pts_to a (Seq.upd s (SZ.v i) x)

fn alloc (#t: Type0) (n: I32.t { I32.v n >= 0 }) (init: t)
  requires emp
  returns a: array t
  ensures pts_to a (Seq.create (I32.v n) init)

fn memcpy_l (#t: Type0) (n: SZ.t)
  (src dst: (a:array t { SZ.v n <= length a }))
  (#p: perm) (#s #d: Ghost.erased (Seq.seq t))
  requires pts_to src #p s ** pts_to dst d
  returns squash (Seq.length s == length src /\ Seq.length d == length dst)
  ensures pts_to src #p s **
    pts_to dst (Seq.append (Seq.slice s 0 (SZ.v n))
                          (Seq.slice d (SZ.v n) (length dst)))
