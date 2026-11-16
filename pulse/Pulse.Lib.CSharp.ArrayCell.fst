module Pulse.Lib.CSharp.ArrayCell
#lang-pulse

/// A local that owns an array and is reassigned (doc/translation.md R34.10): `T[] arr =
/// new T[n]; … Array.Resize(ref arr, m); … return arr;`.
///
/// R6.11a binds an array-owning local immutably to its array, so it cannot be reassigned.
/// This one is a reference cell `c` instead, and `pts_to c s` owns both the cell and the
/// array it currently holds, at contents `s`. Each operation reads the cell and applies
/// the ordinary one (`Pulse.Lib.CSharp.Array`); `resize` replaces the array, dropping the
/// old one as `Array.Resize` leaves it to the garbage collector; `take` hands the array
/// out (for a `return`) and `release` drops it. Nothing here is assumed.

open Pulse
open Pulse.Lib.CSharp.Inhabited

module A = Pulse.Lib.CSharp.Array
module R = Pulse.Lib.Reference
module I32 = FStar.Int32
module Seq = FStar.Seq
module T = FStar.Tactics.V2
module QS = Pulse.Lib.CSharp.QueueStack

let pts_to (#t: Type0) ([@@@mkey] c: R.ref (A.array t)) (s: Seq.seq t) : slprop =
  exists* (a: A.array t). R.pts_to c a ** A.pts_to a s

/// Filling the array in order: writing `b`'s next item at `n` extends the prefix `a` shares
/// with `b` by one (the invariant of a loop that copies an enumeration into the cell).
let upd_extends_prefix (#t: Type0) (a b: Seq.seq t) (n: nat) (x: t)
  : Lemma (requires n < Seq.length a /\ n < Seq.length b /\
                    Seq.equal (Seq.slice a 0 n) (Seq.slice b 0 n) /\ x == Seq.index b n)
          (ensures  Seq.equal (Seq.slice (Seq.upd a n x) 0 (n + 1)) (Seq.slice b 0 (n + 1)))
          [SMTPat (Seq.upd a n x); SMTPat (Seq.equal (Seq.slice a 0 n) (Seq.slice b 0 n))]
  = assert (forall (i: nat). i < n ==> Seq.index (Seq.slice a 0 n) i == Seq.index (Seq.slice b 0 n) i)

ghost
fn intro (#t: Type0) (c: R.ref (A.array t)) (#a: A.array t) (#s: Seq.seq t)
  requires R.pts_to c a ** A.pts_to a s
  ensures  pts_to c s
{
  fold (pts_to c s);
}

/// The array's length, which bounds every index (`arr_length_bound`).
fn length (#t: Type0) (c: R.ref (A.array t)) (#s: Ghost.erased (Seq.seq t))
  preserves pts_to c s
  returns  n : I32.t
  ensures  pure (I32.v n == Seq.length s)
{
  unfold (pts_to c s);
  let a = !c;
  let n = A.length_i32 a;
  fold (pts_to c s);
  n
}

fn read (#t: Type0) (c: R.ref (A.array t)) (i: I32.t)
  (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length s })
  preserves pts_to c s
  returns  x : t
  ensures  pure (x == Seq.index s (I32.v i))
{
  unfold (pts_to c s);
  let a = !c;
  let x = A.read a i;
  fold (pts_to c s);
  x
}

fn write (#t: Type0) (c: R.ref (A.array t)) (i: I32.t) (x: t)
  (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length s })
  requires pts_to c s
  ensures  pts_to c (Seq.upd s (I32.v i) x)
{
  unfold (pts_to c s);
  let a = !c;
  A.write a i x;
  fold (pts_to c (Seq.upd s (I32.v i) x));
}

/// `Array.Resize(ref arr, n)` (R23.4).
fn resize (#t: Type0) {| d: has_default t |} (c: R.ref (A.array t)) (n: I32.t { I32.v n >= 0 })
  (#s: Ghost.erased (Seq.seq t))
  requires pts_to c s
  ensures  pts_to c (QS.resized s (I32.v n) (default_of t))
{
  unfold (pts_to c s);
  let a = !c;
  let b = QS.resize a n;
  drop_ (A.pts_to a s);
  c := b;
  fold (pts_to c (QS.resized s (I32.v n) (default_of t)));
}

/// `return arr;`: the array leaves the cell, which is then the bare cell its scope reclaims.
fn take (#t: Type0) (c: R.ref (A.array t)) (#s: Ghost.erased (Seq.seq t))
  requires pts_to c s
  returns  a : A.array t
  ensures  A.pts_to a s ** (exists* (b: A.array t). R.pts_to c b)
  ensures  pure (Seq.length s < pow2 31)
{
  unfold (pts_to c s);
  let a = !c;
  A.pts_to_len a;
  a
}

/// The local goes out of scope still owning its array, which is dropped.
ghost
fn release (#t: Type0) (c: R.ref (A.array t)) (#s: Seq.seq t)
  requires pts_to c s
  ensures  exists* (b: A.array t). R.pts_to c b
{
  unfold (pts_to c s);
  with a. assert (A.pts_to a s);
  drop_ (A.pts_to a s);
}
