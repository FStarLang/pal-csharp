module Pulse.Lib.CSharp.QueueStack
#lang-pulse

/// What `Stack<T>`, `Queue<T>` and `LinkedList<T>` need beyond `Pulse.Lib.CSharp.Array`
/// (doc/translation.md §23): `Array.Resize`, and the sequence facts their contracts are
/// stated with. Everything here is proved; nothing is assumed.

open Pulse
open Pulse.Lib.CSharp.Inhabited

module A = Pulse.Lib.Array
module I32 = FStar.Int32
module Seq = FStar.Seq
module CS = Pulse.Lib.CSharp.Seq
module CA = Pulse.Lib.CSharp.Array

// ---------------------------------------------------------------------------
// R23.4. `Array.Resize(ref a, n)`.
// ---------------------------------------------------------------------------

/// The contents of `Array.Resize`'s result: `s`'s first cells, then `z`.
let resized (#t: Type) (s: Seq.seq t) (n: nat) (z: t) : Seq.seq t =
  Seq.init n (fun (j: nat { j < n }) -> if j < Seq.length s then Seq.index s j else z)

let resized_length (#t: Type) (s: Seq.seq t) (n: nat) (z: t)
  : Lemma (Seq.length (resized s n z) == n)
          [SMTPat (Seq.length (resized s n z))]
  = ()

/// The prefix that survives a resize, as the slice a model is written with.
let resized_prefix (#t: Type) (s: Seq.seq t) (n: nat) (z: t) (k: nat)
  : Lemma (requires k <= n /\ k <= Seq.length s)
          (ensures  Seq.slice (resized s n z) 0 k == Seq.slice s 0 k)
          [SMTPat (Seq.slice (resized s n z) 0 k)]
  = Seq.lemma_eq_intro (Seq.slice (resized s n z) 0 k) (Seq.slice s 0 k)

/// `Array.Resize(ref a, n)`. The CLR allocates when the length changes and otherwise
/// keeps `a`; reference identity is not modelled (R18.1), so both are a fresh array
/// whose cells are `resized`. The old array is left to the caller, who drops it.
fn resize (#t: Type0) {| d: has_default t |} (a: A.array t) (n: I32.t { I32.v n >= 0 })
  (#p: perm) (#s: Ghost.erased (Seq.seq t))
  preserves A.pts_to a #p s
  returns  b : A.array t
  ensures  A.pts_to b (resized s (I32.v n) (default_of t))
{
  A.pts_to_len a;
  let b = CA.alloc n (default_of t);
  let len = CA.length_i32 a;
  let m = (if I32.lt len n then len else n);
  CA.copy a b m;
  with c. assert (A.pts_to b c);
  Seq.lemma_eq_intro c (resized s (I32.v n) (default_of t));
  rewrite (A.pts_to b c) as (A.pts_to b (resized s (I32.v n) (default_of t)));
  b
}

// ---------------------------------------------------------------------------
// R23.6. `Debug.Assert(a != b)` between two arrays the method holds.
// ---------------------------------------------------------------------------

/// Two arrays held at once, one of them whole, are distinct if either has a cell. Two
/// empty arrays may be one object (`Array.Empty<T>()`), so nothing is concluded about
/// them. The other may be held at a fraction, as a read-only method holds its receiver's.
ghost
fn distinct (#t: Type0) (a b: A.array t) (#p1 #p2: perm) (#s1 #s2: Ghost.erased (Seq.seq t))
  preserves A.pts_to a #p1 s1 ** A.pts_to b #p2 s2
  requires pure ((p1 == 1.0R \/ p2 == 1.0R) /\ (Seq.length s1 > 0 \/ Seq.length s2 > 0))
  ensures  pure (~(a == b))
{
  let same = FStar.IndefiniteDescription.strong_excluded_middle (a == b);
  if same
  {
    rewrite (A.pts_to b #p2 s2) as (A.pts_to a #p2 s2);
    A.gather a;
    A.pts_to_perm_bound a;
    unreachable ()
  }
}
