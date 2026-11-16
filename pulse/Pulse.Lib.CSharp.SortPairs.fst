module Pulse.Lib.CSharp.SortPairs
#lang-pulse

/// R34.22. What `SortedList<K, V>(IDictionary<K, V>, IComparer<K>)` does with a dictionary's
/// pairs: `Array.Sort(keys, values, comparer)`, which sorts the keys and moves each value
/// with its key, and the duplicate test after it. Verified, no admits; the only trusted
/// facts are the comparer axioms of `Order` (R22.30).

open Pulse
open Pulse.Lib.CSharp.Array
open Pulse.Lib.CSharp.Sort

module A = Pulse.Lib.CSharp.Array
module R = Pulse.Lib.Reference
module I32 = FStar.Int32
module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module SD = Pulse.Lib.CSharp.Sorted
module KM = Pulse.Lib.CSharp.KeyMap
module H = Pulse.Lib.CSharp.Heap
module CS = Pulse.Lib.CSharp.Seq

(* ------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* ------------------------------------------------------------------------- *)

/// `SpecKeyMap.Zip(k, v)`: the pairs of two sequences, position by position.
let zip (#a #b: Type) (k: Seq.seq a) (v: Seq.seq b) : Seq.seq (a & b) =
  Seq.init (if Seq.length k <= Seq.length v then Seq.length k else Seq.length v)
    (fun (j: nat { j < Seq.length k /\ j < Seq.length v }) -> (Seq.index k j, Seq.index v j))

let zip_length (#a #b: Type) (k: Seq.seq a) (v: Seq.seq b)
  : Lemma (requires Seq.length k == Seq.length v)
          (ensures Seq.length (zip k v) == Seq.length k)
          [SMTPat (zip k v)]
  = ()

let zip_index (#a #b: Type) (k: Seq.seq a) (v: Seq.seq b) (j: nat)
  : Lemma (requires Seq.length k == Seq.length v /\ j < Seq.length k)
          (ensures Seq.index (zip k v) j == (Seq.index k j, Seq.index v j))
          [SMTPat (Seq.index (zip k v) j)]
  = ()

/// `Pal.Distinct(comparer, s)`: no two elements of `s` are equivalent under `comparer`.
let distinct (#t: Type) (c: O.comparer t) (s: Seq.seq t) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> O.compare c (Seq.index s i) (Seq.index s j) <> 0

/// `SpecKeyMap.DistinctKeys(comparer, pairs)`: no two keys are equivalent.
let distinct_keys (#k #v: Type) (c: O.comparer k) (s: Seq.seq (k & v)) : prop =
  distinct c (KM.keys s)

/// What `Array.Sort(k0, v0, c)` leaves: `k1` in `c`'s order, and the pairs of `k1` and
/// `v1` a permutation of those of `k0` and `v0`, and so of whatever those permute.
let sorted_pairs (#a #b: Type) (k0: Seq.seq a) (v0: Seq.seq b) (k1: Seq.seq a) (v1: Seq.seq b)
    (c: O.comparer a) : prop =
  Seq.length k0 == Seq.length v0 /\ Seq.length k1 == Seq.length k0 /\ Seq.length v1 == Seq.length v0 /\
  SD.sorted (SD.or_default c) k1 /\
  permutation (zip k0 v0) (zip k1 v1) /\
  (forall (s: Seq.seq (a & b)).{:pattern permutation s (zip k1 v1)}
     permutation s (zip k0 v0) ==> permutation s (zip k1 v1))

(* ------------------------------------------------------------------------- *)
(* Lemmas                                                                     *)
(* ------------------------------------------------------------------------- *)

let zip_swap (#a #b: Type) (k: Seq.seq a) (v: Seq.seq b) (i j: nat)
  : Lemma (requires Seq.length k == Seq.length v /\ i < Seq.length k /\ j < Seq.length k)
          (ensures zip (swap k i j) (swap v i j) == swap (zip k v) i j)
  = Seq.lemma_eq_intro (zip (swap k i j) (swap v i j)) (swap (zip k v) i j)

/// The pairs are the zip of their keys and their values.
let zip_keys_values (#k #v: Type) (s: Seq.seq (k & v))
  : Lemma (zip (KM.keys s) (KM.values s) == s)
  = Seq.lemma_eq_intro (zip (KM.keys s) (KM.values s)) s

/// R34.22. `SpecKeyMap.Zip(Keys(s), Values(s))` is a permutation of `s`: what a
/// dictionary of at most one pair, copied and not sorted, leaves.
let permutation_zip_keys_values (#k #v: Type) (s: Seq.seq (k & v))
  : Lemma (permutation s (zip (KM.keys s) (KM.values s)))
  = zip_keys_values s; permutation_refl s

/// A copy of a whole sequence over a whole array is the sequence.
let copied_at_whole (#t: Type) (s d: Seq.seq t) (n: nat)
  : Lemma (requires n == Seq.length s /\ Seq.length s == Seq.length d)
          (ensures CS.copied_at s 0 d 0 n == s)
          [SMTPat (CS.copied_at s 0 d 0 n)]
  = Seq.lemma_eq_intro (CS.copied_at s 0 d 0 n) s

/// R34.22. Keys and values copied from `s`, in its order, pair up to `s`.
let copied_pairs (#k #v: Type) (s: Seq.seq (k & v)) (ks: Seq.seq k) (vs: Seq.seq v)
  : Lemma (requires Seq.length ks == Seq.length s /\ Seq.length vs == Seq.length s /\
                    (Seq.length s == 0 \/ (ks == KM.keys s /\ vs == KM.values s)))
          (ensures permutation s (zip ks vs))
  = Seq.lemma_eq_intro ks (KM.keys s);
    Seq.lemma_eq_intro vs (KM.values s);
    permutation_zip_keys_values s

let permutation_through (#t: Type) (s a b: Seq.seq t)
  : Lemma (requires permutation a b)
          (ensures permutation s a ==> permutation s b)
  = introduce permutation s a ==> permutation s b
    with H.permutation_trans s a b

let permutations_through (#t: Type) (a b: Seq.seq t)
  : Lemma (requires permutation a b)
          (ensures forall (s: Seq.seq t).{:pattern permutation s b} permutation s a ==> permutation s b)
  = introduce forall (s: Seq.seq t). permutation s a ==> permutation s b
    with permutation_through s a b

/// Two positions of a permutation's image are two positions of its source.
let permutation_pair (#t: Type) (a b: Seq.seq t) (i j: nat)
  : Lemma (requires permutation a b /\ i < j /\ j < Seq.length b)
          (ensures exists (p q: nat). p <> q /\ p < Seq.length a /\ q < Seq.length a /\
                     Seq.index b i == Seq.index a p /\ Seq.index b j == Seq.index a q)
  = reveal_opaque (`%permutation) (permutation #t);
    eliminate exists (f: nat -> nat). is_bij (Seq.length a) f /\
        (forall (k: nat). k < Seq.length a ==> Seq.index b k == Seq.index a (f k))
    with introduce exists (p q: nat). p <> q /\ p < Seq.length a /\ q < Seq.length a /\
                     Seq.index b i == Seq.index a p /\ Seq.index b j == Seq.index a q
      with (f i) (f j) and ()

/// R34.22. Two equivalent keys among the sorted pairs are two among the source pairs.
let dup_found (#k #v: Type) (s: Seq.seq (k & v)) (ks: Seq.seq k) (vs: Seq.seq v)
    (c: O.comparer k) (i: nat)
  : Lemma (requires Seq.length ks == Seq.length vs /\ permutation s (zip ks vs) /\
                    0 < i /\ i < Seq.length ks /\
                    O.compare c (Seq.index ks (i - 1)) (Seq.index ks i) == 0)
          (ensures ~(distinct_keys c s))
  = reveal_opaque (`%permutation) (permutation #(k & v));
    permutation_pair s (zip ks vs) (i - 1) i;
    eliminate exists (p q: nat). p <> q /\ p < Seq.length s /\ q < Seq.length s /\
                     Seq.index (zip ks vs) (i - 1) == Seq.index s p /\ Seq.index (zip ks vs) i == Seq.index s q
    with begin
      assert (Seq.index (KM.keys s) p == Seq.index ks (i - 1));
      assert (Seq.index (KM.keys s) q == Seq.index ks i);
      if p < q then ()
      else O.compare_antisym c (Seq.index ks (i - 1)) (Seq.index ks i)
    end

/// R34.22. A sorted sequence whose prefix `[0, i)` is strictly sorted, with `s[i-1]` and
/// `s[i]` not equivalent, is strictly sorted up to `i + 1`.
let strict_step (#t: Type) (c: O.comparer t) (s: Seq.seq t) (i: nat)
  : Lemma (requires SD.sorted c s /\ 0 < i /\ i < Seq.length s /\
                    SD.strictly_sorted c (Seq.slice s 0 i) /\
                    O.compare c (Seq.index s (i - 1)) (Seq.index s i) <> 0)
          (ensures SD.strictly_sorted c (Seq.slice s 0 (i + 1)))
  = let aux (p q: nat) : Lemma (p < q /\ q < i + 1 ==> O.compare c (Seq.index s p) (Seq.index s q) < 0) =
      if p < q && q < i + 1 then begin
        if q < i then assert (Seq.index (Seq.slice s 0 i) p == Seq.index s p /\
                              Seq.index (Seq.slice s 0 i) q == Seq.index s q)
        else if p = i - 1 then ()
        else begin
          assert (Seq.index (Seq.slice s 0 i) p == Seq.index s p /\
                  Seq.index (Seq.slice s 0 i) (i - 1) == Seq.index s (i - 1));
          O.compare_trans c (Seq.index s p) (Seq.index s (i - 1)) (Seq.index s i)
        end
      end
    in
    Classical.forall_intro_2 aux

(* ------------------------------------------------------------------------- *)
(* Implementation                                                             *)
(* ------------------------------------------------------------------------- *)

#push-options "--z3rlimit 40"
/// `Array.Sort(keys, values, comparer)`, over whole arrays of one length (the CLR's
/// precondition is `values.Length >= keys.Length`). An insertion sort, as `Sort.sort`.
fn sort_pairs (#a #b: Type0) (ka: array a) (va: array b) (c: O.comparer a)
  (#k0: Ghost.erased (Seq.seq a)) (#v0: Ghost.erased (Seq.seq b) { Seq.length v0 == Seq.length k0 })
  requires A.pts_to ka k0 ** A.pts_to va v0
  ensures  exists* k1 v1. A.pts_to ka k1 ** A.pts_to va v1 ** pure (sorted_pairs k0 v0 k1 v1 c)
{
  A.pts_to_len ka;
  A.pts_to_len va;
  arr_length_bound ka;
  let cc = SD.or_default c;
  let hi = length_i32 ka;
  permutation_refl (zip k0 v0);
  let mut k = 0l;
  while (I32.lt !k hi)
    invariant exists* vk s t.
      R.pts_to k vk ** A.pts_to ka s ** A.pts_to va t **
      pure (0 <= I32.v vk /\ I32.v vk <= I32.v hi /\ Seq.length s == Seq.length k0 /\
            Seq.length t == Seq.length v0 /\
            permutation (zip k0 v0) (zip s t) /\
            sorted_in cc s 0 (I32.v vk))
    decreases (I32.v hi - I32.v !k)
  {
    let vk = !k;
    with s. assert (A.pts_to ka s);
    ins_init cc s 0 (I32.v vk);
    let mut j = vk;
    while (
      let vj = !j;
      if (I32.gt vj 0l) {
        let x = read ka (I32.sub vj 1l);
        let y = read ka vj;
        I32.gt (SD.compare_i32 cc x y) 0l
      } else {
        false
      })
      invariant exists* vj s' t'.
        R.pts_to j vj ** A.pts_to ka s' ** A.pts_to va t' **
        pure (0 <= I32.v vj /\ I32.v vj <= I32.v vk /\ Seq.length s' == Seq.length k0 /\
              Seq.length t' == Seq.length v0 /\
              permutation (zip k0 v0) (zip s' t') /\
              ins_inv cc s' 0 (I32.v vk + 1) (I32.v vj))
      decreases (I32.v !j)
    {
      let vj = !j;
      with s' t'. assert (A.pts_to ka s' ** A.pts_to va t');
      let x = read ka (I32.sub vj 1l);
      let y = read ka vj;
      let u = read va (I32.sub vj 1l);
      let w = read va vj;
      ins_step cc s' 0 (I32.v vk + 1) (I32.v vj);
      zip_swap s' t' (I32.v vj - 1) (I32.v vj);
      permutation_swap (zip k0 v0) (zip s' t') (I32.v vj - 1) (I32.v vj);
      write ka (I32.sub vj 1l) y;
      write ka vj x;
      write va (I32.sub vj 1l) w;
      write va vj u;
      with s'' t''. assert (A.pts_to ka s'' ** A.pts_to va t'');
      Seq.lemma_eq_elim s'' (swap s' (I32.v vj - 1) (I32.v vj));
      Seq.lemma_eq_elim t'' (swap t' (I32.v vj - 1) (I32.v vj));
      j := I32.sub vj 1l;
    };
    let vj = !j;
    with s'. assert (A.pts_to ka s');
    ins_done cc s' 0 (I32.v vk + 1) (I32.v vj);
    k := I32.add vk 1l;
  };
  with s t. assert (A.pts_to ka s ** A.pts_to va t);
  assert (pure (sorted_in cc s 0 (Seq.length s)));
  assert (pure (SD.sorted cc s));
  permutations_through (zip k0 v0) (zip s t);
  ()
}
#pop-options
