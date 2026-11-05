module Pulse.Lib.CSharp.Sort
#lang-pulse

/// Sorting an array range with a comparer (doc/translation.md R26.7): what
/// `Array.Sort(a, lo, n, comparer)` is specified to do. Verified, no admits; the only
/// trusted facts are the comparer axioms of `Order` (R22.30).

open Pulse
open Pulse.Lib.CSharp.Array

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module I32 = FStar.Int32
module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module SD = Pulse.Lib.CSharp.Sorted

(* ------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* ------------------------------------------------------------------------- *)

/// `s[lo..hi)` is in `c`'s order.
let sorted_in (#t: Type) (c: O.comparer t) (s: Seq.seq t) (lo hi: nat) : prop =
  forall (i j: nat).{:pattern (Seq.index s i); (Seq.index s j)}
    lo <= i /\ i <= j /\ j < hi /\ hi <= Seq.length s ==>
    O.compare c (Seq.index s i) (Seq.index s j) <= 0

let is_bij (n: nat) (f: nat -> nat) : prop =
  (forall (i: nat). i < n ==> f i < n) /\
  (forall (i j: nat). i < n /\ j < n /\ f i == f j ==> i == j)

/// `Pal.Permutation(a, b)`: `b` is `a` reordered. Stated by a bijection on positions
/// rather than by counting, since `T` need not have a decidable equality.
[@@"opaque_to_smt"]
let permutation (#t: Type) (a b: Seq.seq t) : prop =
  Seq.length a == Seq.length b /\
  (exists (f: nat -> nat). is_bij (Seq.length a) f /\
     (forall (i: nat). i < Seq.length a ==> Seq.index b i == Seq.index a (f i)))

/// Outside `[lo, hi)`, `s1` is `s0`.
let unchanged_outside (#t: Type) (s0 s1: Seq.seq t) (lo hi: nat) : prop =
  Seq.length s0 == Seq.length s1 /\
  (forall (k: nat).{:pattern (Seq.index s1 k)}
     k < Seq.length s1 /\ (k < lo \/ hi <= k) ==> Seq.index s1 k == Seq.index s0 k)

/// `Pal.SortedRange(s0, s1, lo, n, comparer)`: `s1` is `s0` with `[lo, lo+n)` sorted.
let sorted_range (#t: Type) (s0 s1: Seq.seq t) (lo n: int) (c: O.comparer t) : prop =
  0 <= lo /\ 0 <= n /\ lo + n <= Seq.length s0 /\
  unchanged_outside s0 s1 lo (lo + n) /\
  sorted_in (SD.or_default c) s1 lo (lo + n) /\
  permutation (Seq.slice s0 lo (lo + n)) (Seq.slice s1 lo (lo + n))

(* ------------------------------------------------------------------------- *)
(* Lemmas                                                                     *)
(* ------------------------------------------------------------------------- *)

let swap (#t: Type) (s: Seq.seq t) (i j: nat { i < Seq.length s /\ j < Seq.length s })
  : Seq.seq t
  = Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)

let permutation_refl (#t: Type) (a: Seq.seq t)
  : Lemma (permutation a a)
  = reveal_opaque (`%permutation) (permutation #t);
    let f (i: nat) : nat = i in
    assert (is_bij (Seq.length a) f);
    assert (forall (i: nat). i < Seq.length a ==> Seq.index a i == Seq.index a (f i))

let sw (i j k: nat) : nat = if k = i then j else if k = j then i else k

let bij_sw (n: nat) (f: nat -> nat) (i j: nat)
  : Lemma (requires is_bij n f /\ i < n /\ j < n)
          (ensures is_bij n (fun k -> f (sw i j k)))
  = let g (k: nat) : nat = f (sw i j k) in
    introduce forall (k1 k2: nat). k1 < n /\ k2 < n /\ g k1 == g k2 ==> k1 == k2
    with introduce _ ==> _ with begin
      assert (sw i j k1 < n /\ sw i j k2 < n);
      assert (sw i j k1 == sw i j k2)
    end

let permutation_swap_with (#t: Type) (a b: Seq.seq t) (i j: nat) (f: nat -> nat)
  : Lemma (requires Seq.length a == Seq.length b /\ i < Seq.length b /\ j < Seq.length b /\
                    is_bij (Seq.length a) f /\
                    (forall (k: nat). k < Seq.length a ==> Seq.index b k == Seq.index a (f k)))
          (ensures permutation a (swap b i j))
  = let n = Seq.length a in
    let b' = swap b i j in
    assert (Seq.length b' == n);
    let g (k: nat) : nat = f (sw i j k) in
    bij_sw n f i j;
    assert (is_bij n g);
    let aux (k: nat) : Lemma (k < n ==> Seq.index b' k == Seq.index a (g k)) =
      if k < n then assert (Seq.index b' k == Seq.index b (sw i j k))
    in
    Classical.forall_intro aux;
    introduce exists (g: nat -> nat). is_bij n g /\
      (forall (k: nat). k < n ==> Seq.index b' k == Seq.index a (g k))
    with g and ();
    reveal_opaque (`%permutation) (permutation #t);
    assert (permutation a b')

let permutation_swap (#t: Type) (a b: Seq.seq t) (i j: nat)
  : Lemma (requires permutation a b /\ i < Seq.length b /\ j < Seq.length b)
          (ensures permutation a (swap b i j))
  = reveal_opaque (`%permutation) (permutation #t);
    eliminate exists (f: nat -> nat). is_bij (Seq.length a) f /\
        (forall (k: nat). k < Seq.length a ==> Seq.index b k == Seq.index a (f k))
    with permutation_swap_with a b i j f

let slice_swap (#t: Type) (s: Seq.seq t) (lo hi i j: nat)
  : Lemma (requires lo <= i /\ i < hi /\ lo <= j /\ j < hi /\ hi <= Seq.length s)
          (ensures Seq.slice (swap s i j) lo hi == swap (Seq.slice s lo hi) (i - lo) (j - lo))
  = Seq.lemma_eq_elim (Seq.slice (swap s i j) lo hi) (swap (Seq.slice s lo hi) (i - lo) (j - lo))

/// The inner loop of insertion sort: `s[lo..hi)` is sorted but for position `j`,
/// whose element is no greater than any after it.
[@@"opaque_to_smt"]
let ins_inv (#t: Type) (c: O.comparer t) (s: Seq.seq t) (lo hi j: nat) : prop =
  lo <= j /\ j < hi /\ hi <= Seq.length s /\
  (forall (p q: nat).{:pattern (Seq.index s p); (Seq.index s q)}
     lo <= p /\ p < q /\ q < hi /\ p <> j /\ q <> j ==>
     O.compare c (Seq.index s p) (Seq.index s q) <= 0) /\
  (forall (q: nat).{:pattern (Seq.index s q)}
     j < q /\ q < hi ==> O.compare c (Seq.index s j) (Seq.index s q) <= 0)

let ins_init (#t: Type) (c: O.comparer t) (s: Seq.seq t) (lo j: nat)
  : Lemma (requires lo <= j /\ j < Seq.length s /\ sorted_in c s lo j)
          (ensures ins_inv c s lo (j + 1) j)
  = reveal_opaque (`%ins_inv) (ins_inv #t)

let ins_step (#t: Type) (c: O.comparer t) (s: Seq.seq t) (lo hi j: nat)
  : Lemma (requires ins_inv c s lo hi j /\ lo < j /\ j < hi /\ hi <= Seq.length s /\
                    O.compare c (Seq.index s (j - 1)) (Seq.index s j) > 0)
          (ensures ins_inv c (swap s (j - 1) j) lo hi (j - 1))
  = reveal_opaque (`%ins_inv) (ins_inv #t);
    O.compare_antisym c (Seq.index s (j - 1)) (Seq.index s j)

let ins_done (#t: Type) (c: O.comparer t) (s: Seq.seq t) (lo hi j: nat)
  : Lemma (requires ins_inv c s lo hi j /\ lo <= j /\ j < hi /\ hi <= Seq.length s /\
                    (j == lo \/ O.compare c (Seq.index s (j - 1)) (Seq.index s j) <= 0))
          (ensures sorted_in c s lo hi)
  = reveal_opaque (`%ins_inv) (ins_inv #t);
    if j > lo then begin
      let aux (p: nat) : Lemma (lo <= p /\ p < j - 1 ==> O.compare c (Seq.index s p) (Seq.index s j) <= 0) =
        if lo <= p && p < j - 1 then
          O.compare_trans c (Seq.index s p) (Seq.index s (j - 1)) (Seq.index s j)
      in
      Classical.forall_intro aux
    end

/// `List<T>.Items` is a prefix of the backing array: a sort of a range inside the
/// prefix is one of the prefix.
let sorted_range_prefix (#t: Type) (s0 s1: Seq.seq t) (lo n: int) (c: O.comparer t) (m: nat)
  : Lemma (requires sorted_range s0 s1 lo n c /\ lo + n <= m /\ m <= Seq.length s0)
          (ensures sorted_range (Seq.slice s0 0 m) (Seq.slice s1 0 m) lo n c)
          [SMTPat (sorted_range (Seq.slice s0 0 m) (Seq.slice s1 0 m) lo n c)]
  = assert (Seq.slice (Seq.slice s0 0 m) lo (lo + n) `Seq.equal` Seq.slice s0 lo (lo + n));
    assert (Seq.slice (Seq.slice s1 0 m) lo (lo + n) `Seq.equal` Seq.slice s1 lo (lo + n))

/// A range of at most one element is already sorted: `List<T>.Sort` skips the call.
let sorted_range_small (#t: Type) (s: Seq.seq t) (lo n: int) (c: O.comparer t)
  : Lemma (requires 0 <= lo /\ 0 <= n /\ n <= 1 /\ lo + n <= Seq.length s)
          (ensures sorted_range s s lo n c)
          [SMTPat (sorted_range s s lo n c)]
  = permutation_refl (Seq.slice s lo (lo + n));
    if n = 1 then O.compare_refl (SD.or_default c) (Seq.index s lo)

(* ------------------------------------------------------------------------- *)
(* Implementations                                                            *)
(* ------------------------------------------------------------------------- *)

#push-options "--z3rlimit 40"
/// `Array.Sort(a, lo, n, comparer)`. An insertion sort: the BCL's introsort is not
/// what runs in the proof, but a sort's contract does not say which sort (R26.7).
fn sort (#t: Type0) (a: array t) (lo n: I32.t) (c: O.comparer t)
  (#s0: Ghost.erased (Seq.seq t) { I32.v lo >= 0 /\ I32.v n >= 0 /\ I32.v lo + I32.v n <= Seq.length s0 })
  requires A.pts_to a s0
  ensures  exists* s1. A.pts_to a s1 ** pure (sorted_range s0 s1 (I32.v lo) (I32.v n) c)
{
  A.pts_to_len a;
  arr_length_bound a;
  let cc = SD.or_default c;
  let hi = I32.add lo n;
  permutation_refl (Seq.slice s0 (I32.v lo) (I32.v hi));
  let mut k = lo;
  while (I32.lt !k hi)
    invariant exists* vk s.
      R.pts_to k vk ** A.pts_to a s **
      pure (I32.v lo <= I32.v vk /\ I32.v vk <= I32.v hi /\ Seq.length s == Seq.length s0 /\
            unchanged_outside s0 s (I32.v lo) (I32.v hi) /\
            permutation (Seq.slice s0 (I32.v lo) (I32.v hi)) (Seq.slice s (I32.v lo) (I32.v hi)) /\
            sorted_in cc s (I32.v lo) (I32.v vk))
    decreases (I32.v hi - I32.v !k)
  {
    let vk = !k;
    with s. assert (A.pts_to a s);
    ins_init cc s (I32.v lo) (I32.v vk);
    let mut j = vk;
    while (
      let vj = !j;
      if (I32.gt vj lo) {
        let x = read a (I32.sub vj 1l);
        let y = read a vj;
        I32.gt (SD.compare_i32 cc x y) 0l
      } else {
        false
      })
      invariant exists* vj s'.
        R.pts_to j vj ** A.pts_to a s' **
        pure (I32.v lo <= I32.v vj /\ I32.v vj <= I32.v vk /\ Seq.length s' == Seq.length s0 /\
              unchanged_outside s0 s' (I32.v lo) (I32.v hi) /\
              permutation (Seq.slice s0 (I32.v lo) (I32.v hi)) (Seq.slice s' (I32.v lo) (I32.v hi)) /\
              ins_inv cc s' (I32.v lo) (I32.v vk + 1) (I32.v vj))
      decreases (I32.v !j)
    {
      let vj = !j;
      with s'. assert (A.pts_to a s');
      let x = read a (I32.sub vj 1l);
      let y = read a vj;
      ins_step cc s' (I32.v lo) (I32.v vk + 1) (I32.v vj);
      slice_swap s' (I32.v lo) (I32.v hi) (I32.v vj - 1) (I32.v vj);
      permutation_swap (Seq.slice s0 (I32.v lo) (I32.v hi)) (Seq.slice s' (I32.v lo) (I32.v hi))
        (I32.v vj - 1 - I32.v lo) (I32.v vj - I32.v lo);
      write a (I32.sub vj 1l) y;
      write a vj x;
      with s''. assert (A.pts_to a s'');
      assert (pure (s'' `Seq.equal` swap s' (I32.v vj - 1) (I32.v vj)));
      Seq.lemma_eq_elim s'' (swap s' (I32.v vj - 1) (I32.v vj));
      j := I32.sub vj 1l;
    };
    let vj = !j;
    with s'. assert (A.pts_to a s');
    ins_done cc s' (I32.v lo) (I32.v vk + 1) (I32.v vj);
    k := I32.add vk 1l;
  };
  ()
}

#pop-options
