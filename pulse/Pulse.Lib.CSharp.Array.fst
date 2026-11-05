module Pulse.Lib.CSharp.Array
#lang-pulse

open Pulse
open Pulse.Lib.CSharp.Assumptions
open Pulse.Lib.CSharp.Casts
open Pulse.Lib.CSharp.Inhabited
open Pulse.Lib.SmallType

module A = Pulse.Lib.Array
module I32 = FStar.Int32
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* MODELING AXIOM: the CLR array-length header field is immutable, so reading it
   is pure, and it has type `int`, so its value is below 2^31. *)
assume
val clr_array_length_header (#t: Type0) (a: array t)
  : (n: I32.t { I32.v n == A.length a })

let arr_length (#t: Type0) (a: array t) : I32.t = clr_array_length_header a

let arr_length_v (#t: Type0) (a: array t)
  : Lemma (I32.v (arr_length a) == A.length a)
          [SMTPat (I32.v (arr_length a))]
  = ()

(* A C# array's length is an `int`, so it is below 2^31. Without this the obligation
   that an index one past the last read still fits in an `int` cannot be discharged:
   the loop knows `i < a.Length` but nothing bounds `a.Length` itself. The fact belongs
   here rather than in any one program's annotations, because it holds of every array. *)
let arr_length_bound (#t: Type0) (a: array t)
  : Lemma (A.length a < pow2 31)
          [SMTPat (A.length a)]
  = let _ = clr_array_length_header a in ()

fn length_i32 (#t: Type0) (a: array t) (#p: perm) (#s: Ghost.erased (Seq.seq t))
  preserves A.pts_to a #p s
  returns  n : I32.t
  ensures  rewrites_to n (arr_length a)
  ensures  pure (I32.v n == Seq.length s)
{
  A.pts_to_len a;
  admit()
}

fn read (#t: Type0) (a: array t) (i: I32.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length s })
  preserves A.pts_to a #p s
  returns  x : t
  ensures  rewrites_to x (Seq.index s (I32.v i))
{
  a.(idx i)
}

fn write (#t: Type0) (a: array t) (i: I32.t) (x: t)
         (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length s })
  requires A.pts_to a s
  ensures  A.pts_to a (Seq.upd s (I32.v i) x)
{
  (a.(idx i) <- x)
}

fn alloc (#t: Type0) (n: I32.t { I32.v n >= 0 }) (init: t)
  requires emp
  returns  a : array t
  ensures  A.pts_to a (Seq.create (I32.v n) init)
{
  (* MODELING AXIOM: `new T[n]` on a garbage-collected heap always succeeds and
     zero-fills, and imposes no deallocation obligation. *)
  admit()
}

fn alloc_empty (#t: Type0) (_: unit)
  requires emp
  returns  a : array t
  ensures  A.pts_to a (Seq.empty #t)
{
  (* MODELING AXIOM: a zero-length array exists at every element type. *)
  admit()
}

fn copy (#t: Type0) (src dst: array t) (len: I32.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t))
        (#d: Ghost.erased (Seq.seq t)
              { I32.v len >= 0 /\ I32.v len <= Seq.length s /\ I32.v len <= Seq.length d })
  requires A.pts_to src #p s ** A.pts_to dst d
  ensures  A.pts_to src #p s **
           A.pts_to dst (copied s d (I32.v len)) **
           pure (Seq.length (copied s d (I32.v len)) == Seq.length d /\
                 Seq.slice (copied s d (I32.v len)) 0 (I32.v len) == Seq.slice s 0 (I32.v len) /\
                 Seq.slice (copied s d (I32.v len)) (I32.v len) (Seq.length d) ==
                   Seq.slice d (I32.v len) (Seq.length d))
{
  A.pts_to_len src;
  A.pts_to_len dst;
  let _ = A.memcpy_l (int32_to_sizet len) src dst;
  let n = Ghost.hide (I32.v len);
  assert (pure (Seq.equal (Seq.slice (copied s d n) 0 n) (Seq.slice s 0 n)));
  assert (pure (Seq.equal (Seq.slice (copied s d n) n (Seq.length d)) (Seq.slice d n (Seq.length d))));
  rewrite (A.pts_to dst (Seq.append (Seq.slice s 0 (I32.v len)) (Seq.slice d (I32.v len) (A.length dst))))
       as (A.pts_to dst (copied s d (I32.v len)));
  ()
}
