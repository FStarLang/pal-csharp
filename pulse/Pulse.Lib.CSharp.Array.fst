module Pulse.Lib.CSharp.Array
#lang-pulse

open Pulse
open Pulse.Lib.CSharp.Assumptions
open Pulse.Lib.CSharp.Casts
open Pulse.Lib.CSharp.Inhabited
open Pulse.Lib.SmallType
open Pulse.Lib.CSharp.Array.Base

module A = Pulse.Lib.CSharp.Array.Base
module I32 = FStar.Int32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module R = Pulse.Lib.Reference
module CS = Pulse.Lib.CSharp.Seq

let arr_length (#t: Type0) (a: array t) : I32.t = a.count

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
  = ()

fn length_i32 (#t: Type0) (a: array t) (#p: perm) (#s: Ghost.erased (Seq.seq t))
  preserves A.pts_to a #p s
  returns  n : I32.t
  ensures  rewrites_to n (arr_length a)
  ensures  pure (I32.v n == Seq.length s)
{
  A.pts_to_len a;
  arr_length a
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
  A.alloc n init
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

fn copy_at (#t: Type0) (src: array t) (si: I32.t) (dst: array t) (di: I32.t) (len: I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq t))
  (#d: Ghost.erased (Seq.seq t) {
     I32.v si >= 0 /\ I32.v di >= 0 /\ I32.v len >= 0 /\
     I32.v si + I32.v len <= Seq.length s /\ I32.v di + I32.v len <= Seq.length d })
  requires A.pts_to src #p s ** A.pts_to dst d
  ensures  A.pts_to src #p s ** A.pts_to dst (CS.copied_at s (I32.v si) d (I32.v di) (I32.v len))
{
  A.pts_to_len src; A.pts_to_len dst;
  let mut k = 0l;
  while (I32.lt !k len)
  invariant exists* vk c.
    R.pts_to k vk ** A.pts_to dst c ** A.pts_to src #p s **
    pure (0 <= I32.v vk /\ I32.v vk <= I32.v len /\ Seq.length c == Seq.length d /\
          (forall (j: nat). j < Seq.length d ==>
             Seq.index c j == (if I32.v di <= j && j < I32.v di + I32.v vk
                               then Seq.index s (j - I32.v di + I32.v si) else Seq.index d j)))
  decreases (I32.v len - I32.v !k)
  {
    let vk = !k;
    let x = read src (I32.add si vk);
    write dst (I32.add di vk) x;
    k := I32.add vk 1l;
  };
  with c. assert (A.pts_to dst c);
  assert (pure (Seq.equal c (CS.copied_at s (I32.v si) d (I32.v di) (I32.v len))));
  ()
}

/// The CLR copies as if through a temporary, so the loop runs backward when the
/// destination is above the source and forward otherwise.
fn move (#t: Type0) (a: array t) (si: I32.t) (di: I32.t) (len: I32.t)
  (#s: Ghost.erased (Seq.seq t) {
     I32.v si >= 0 /\ I32.v di >= 0 /\ I32.v len >= 0 /\
     I32.v si + I32.v len <= Seq.length s /\ I32.v di + I32.v len <= Seq.length s })
  requires A.pts_to a s
  ensures  A.pts_to a (CS.copied_at s (I32.v si) s (I32.v di) (I32.v len))
{
  A.pts_to_len a;
  if (I32.lt si di)
  {
    let mut k = len;
    while (I32.gt !k 0l)
    invariant exists* vk c.
      R.pts_to k vk ** A.pts_to a c **
      pure (0 <= I32.v vk /\ I32.v vk <= I32.v len /\ Seq.length c == Seq.length s /\
            (forall (j: nat). j < Seq.length s ==>
               Seq.index c j == (if I32.v di + I32.v vk <= j && j < I32.v di + I32.v len
                                 then Seq.index s (j - I32.v di + I32.v si) else Seq.index s j)))
    decreases (I32.v !k)
    {
      let vk = !k;
      let k' = I32.sub vk 1l;
      let x = read a (I32.add si k');
      write a (I32.add di k') x;
      k := k';
    };
    with c. assert (A.pts_to a c);
    assert (pure (Seq.equal c (CS.copied_at s (I32.v si) s (I32.v di) (I32.v len))));
    ()
  }
  else
  {
    let mut k = 0l;
    while (I32.lt !k len)
    invariant exists* vk c.
      R.pts_to k vk ** A.pts_to a c **
      pure (0 <= I32.v vk /\ I32.v vk <= I32.v len /\ Seq.length c == Seq.length s /\
            (forall (j: nat). j < Seq.length s ==>
               Seq.index c j == (if I32.v di <= j && j < I32.v di + I32.v vk
                                 then Seq.index s (j - I32.v di + I32.v si) else Seq.index s j)))
    decreases (I32.v len - I32.v !k)
    {
      let vk = !k;
      let x = read a (I32.add si vk);
      write a (I32.add di vk) x;
      k := I32.add vk 1l;
    };
    with c. assert (A.pts_to a c);
    assert (pure (Seq.equal c (CS.copied_at s (I32.v si) s (I32.v di) (I32.v len))));
    ()
  }
}

fn clear_with (#t: Type0) (z: t) (a: array t) (i: I32.t) (n: I32.t)
  (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v n >= 0 /\ I32.v i + I32.v n <= Seq.length s })
  requires A.pts_to a s
  ensures  A.pts_to a (CS.cleared z s (I32.v i) (I32.v n))
{
  A.pts_to_len a;
  let mut k = 0l;
  while (I32.lt !k n)
  invariant exists* vk c.
    R.pts_to k vk ** A.pts_to a c **
    pure (0 <= I32.v vk /\ I32.v vk <= I32.v n /\ Seq.length c == Seq.length s /\
          (forall (j: nat). j < Seq.length s ==>
             Seq.index c j == (if I32.v i <= j && j < I32.v i + I32.v vk then z else Seq.index s j)))
  decreases (I32.v n - I32.v !k)
  {
    let vk = !k;
    write a (I32.add i vk) z;
    k := I32.add vk 1l;
  };
  with c. assert (A.pts_to a c);
  assert (pure (Seq.equal c (CS.cleared z s (I32.v i) (I32.v n))));
  ()
}

fn reverse (#t: Type0) (a: array t) (i: I32.t) (n: I32.t)
  (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v n >= 0 /\ I32.v i + I32.v n <= Seq.length s })
  requires A.pts_to a s
  ensures  A.pts_to a (CS.reversed s (I32.v i) (I32.v n))
{
  A.pts_to_len a;
  let mut k = 0l;
  let half = I32.div n 2l;
  while (I32.lt !k half)
  invariant exists* vk c.
    R.pts_to k vk ** A.pts_to a c **
    pure (0 <= I32.v vk /\ I32.v vk <= I32.v half /\ Seq.length c == Seq.length s /\
          (forall (j: nat). j < Seq.length s ==>
             Seq.index c j == (if (I32.v i <= j && j < I32.v i + I32.v vk) ||
                                  (I32.v i + I32.v n - I32.v vk <= j && j < I32.v i + I32.v n)
                               then Seq.index s (2 * I32.v i + I32.v n - 1 - j) else Seq.index s j)))
  decreases (I32.v half - I32.v !k)
  {
    let vk = !k;
    let lo = I32.add i vk;
    let hi = I32.sub (I32.add i (I32.sub n 1l)) vk;
    let x = read a lo;
    let y = read a hi;
    write a lo y;
    write a hi x;
    k := I32.add vk 1l;
  };
  with c. assert (A.pts_to a c);
  assert (pure (Seq.equal c (CS.reversed s (I32.v i) (I32.v n))));
  ()
}

fn index_of (#t: Type0) (a: array t) (x: t) (i: I32.t) (n: I32.t)
  (#p: perm)
  (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v n >= 0 /\ I32.v i + I32.v n <= Seq.length s })
  preserves A.pts_to a #p s
  returns  r: I32.t
  ensures  pure (I32.v r == CS.index_of s x (I32.v i) (I32.v n))
{
  A.pts_to_len a;
  let mut k = i;
  let mut r = -1l;
  while (I32.lt !k (I32.add i n))
  invariant exists* vk vr.
    R.pts_to k vk ** R.pts_to r vr ** A.pts_to a #p s **
    pure (I32.v i <= I32.v vk /\ I32.v vk <= I32.v i + I32.v n /\
          (I32.v vk < I32.v i + I32.v n ==> I32.v vr = -1) /\
          (if I32.v vr = -1
           then CS.index_of s x (I32.v i) (I32.v n) == CS.index_of s x (I32.v vk) (I32.v i + I32.v n - I32.v vk)
           else I32.v vr == CS.index_of s x (I32.v i) (I32.v n)))
  decreases (I32.v i + I32.v n - I32.v !k)
  {
    let vk = !k;
    let y = read a vk;
    if (Pulse.Lib.CSharp.Bcl.default_equals y x) { r := vk; k := I32.add i n } else { k := I32.add vk 1l }
  };
  !r
}

fn last_index_of_lo (#t: Type0) (a: array t) (x: t) (lo: I32.t) (n: I32.t)
  (#p: perm)
  (#s: Ghost.erased (Seq.seq t) { I32.v lo >= 0 /\ I32.v n >= 0 /\ I32.v lo + I32.v n <= Seq.length s })
  preserves A.pts_to a #p s
  returns  r: I32.t
  ensures  pure (I32.v r == CS.last_index_of s x (I32.v lo) (I32.v n))
{
  A.pts_to_len a;
  let mut k = n;
  let mut r = -1l;
  while (I32.gt !k 0l)
  invariant exists* vk vr.
    R.pts_to k vk ** R.pts_to r vr ** A.pts_to a #p s **
    pure (0 <= I32.v vk /\ I32.v vk <= I32.v n /\
          (I32.v vk > 0 ==> I32.v vr = -1) /\
          (if I32.v vr = -1
           then CS.last_index_of s x (I32.v lo) (I32.v n) == CS.last_index_of s x (I32.v lo) (I32.v vk)
           else I32.v vr == CS.last_index_of s x (I32.v lo) (I32.v n)))
  decreases (I32.v !k)
  {
    let vk = !k;
    let y = read a (I32.add lo (I32.sub vk 1l));
    if (Pulse.Lib.CSharp.Bcl.default_equals y x) { r := I32.add lo (I32.sub vk 1l); k := 0l } else { k := I32.sub vk 1l }
  };
  !r
}

fn clear (#t: Type0) {| d: has_default t |} (a: array t) (i: I32.t) (n: I32.t)
  (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v n >= 0 /\ I32.v i + I32.v n <= Seq.length s })
  requires A.pts_to a s
  ensures  A.pts_to a (CS.cleared (default_of t) s (I32.v i) (I32.v n))
{
  clear_with (default_of t) a i n
}

/// `Array.LastIndexOf(a, x, index, count)`: the last match in `[index-count+1, index]`.
fn last_index_of (#t: Type0) (a: array t) (x: t) (index: I32.t) (count: I32.t)
  (#p: perm)
  (#s: Ghost.erased (Seq.seq t) {
     I32.v count >= 0 /\ I32.v index - I32.v count + 1 >= 0 /\ I32.v index < Seq.length s })
  preserves A.pts_to a #p s
  returns  r: I32.t
  ensures  pure (I32.v r == CS.last_index_of s x (I32.v index - I32.v count + 1) (I32.v count))
{
  A.pts_to_len a;
  last_index_of_lo a x (I32.add (I32.sub index count) 1l) count
}
