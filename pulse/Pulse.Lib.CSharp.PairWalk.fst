module Pulse.Lib.CSharp.PairWalk

/// R32.11. A walk of a set of pairs whose callback copies each pair's key, or each pair's
/// value, into an array: the protocol of `SortedDictionary`'s `KeyCollection.CopyTo` and
/// `ValueCollection.CopyTo`, and what it leaves once the walk is over.

module Seq = FStar.Seq
module CS = Pulse.Lib.CSharp.Seq
module KM = Pulse.Lib.CSharp.KeyMap
open Pulse.Lib.CSharp.RegionWalk

/// The callback copied `f` of the pair of each call into `a` from `i0`, its cursor now at
/// `idx`, and returned true each time; `a0` is what `a` held before.
let copied_map (#k #v #b #u: Type0) (f: (k & v) -> u) (tr: Seq.seq (((k & v) & b) & bool))
    (a0 a: Seq.seq u) (i0 idx: int) : prop =
  0 <= i0 /\ Seq.length a == Seq.length a0 /\ idx - i0 == Seq.length tr /\
  (forall (n: nat). n < Seq.length tr ==> snd (Seq.index tr n) == true) /\
  (forall (j: nat). j < Seq.length a ==>
     Seq.index a j == (if i0 <= j && j < idx then f (tkey (Seq.index tr (j - i0))) else Seq.index a0 j))

let copied_keys (#k #v #b: Type0) (tr: Seq.seq (((k & v) & b) & bool)) (a0 a: Seq.seq k) (i0 idx: int) : prop =
  copied_map #k #v #b #k fst tr a0 a i0 idx

let copied_values (#k #v #b: Type0) (tr: Seq.seq (((k & v) & b) & bool)) (a0 a: Seq.seq v) (i0 idx: int) : prop =
  copied_map #k #v #b #v snd tr a0 a i0 idx

/// A walk whose callback only returns true went through every pair: `a` is `a0` with `f` of
/// each pair, in order, from `i0`.
let copied_map_walked (#k #v #b #u: Type0) (f: (k & v) -> u) (ps: Seq.seq (k & v))
    (tr: Seq.seq (((k & v) & b) & bool)) (res: bool) (a0 a: Seq.seq u) (i0 idx: int)
  : Lemma (requires walked ps tr res /\ copied_map f tr a0 a i0 idx /\ i0 + Seq.length ps <= Seq.length a0)
          (ensures Seq.length tr == Seq.length ps /\
                   (forall (j: nat). j < Seq.length a ==>
                      Seq.index a j == (if i0 <= j && j < i0 + Seq.length ps then f (Seq.index ps (j - i0))
                                        else Seq.index a0 j)))
  = if not res then begin
      let n = Seq.length tr in
      assert (snd (Seq.index tr (n - 1)) == true)
    end

let copied_keys_walked (#k #v #b: Type0) (ps: Seq.seq (k & v)) (tr: Seq.seq (((k & v) & b) & bool))
    (res: bool) (a0 a: Seq.seq k) (i0 idx: int)
  : Lemma (requires walked ps tr res /\ copied_keys tr a0 a i0 idx /\ i0 + Seq.length ps <= Seq.length a0)
          (ensures a == CS.splice a0 i0 (i0 + Seq.length ps) (KM.keys ps))
          [SMTPat (walked ps tr res); SMTPat (copied_keys tr a0 a i0 idx)]
  = copied_map_walked fst ps tr res a0 a i0 idx;
    Seq.lemma_eq_intro a (CS.splice a0 i0 (i0 + Seq.length ps) (KM.keys ps))

let copied_values_walked (#k #v #b: Type0) (ps: Seq.seq (k & v)) (tr: Seq.seq (((k & v) & b) & bool))
    (res: bool) (a0 a: Seq.seq v) (i0 idx: int)
  : Lemma (requires walked ps tr res /\ copied_values tr a0 a i0 idx /\ i0 + Seq.length ps <= Seq.length a0)
          (ensures a == CS.splice a0 i0 (i0 + Seq.length ps) (KM.values ps))
          [SMTPat (walked ps tr res); SMTPat (copied_values tr a0 a i0 idx)]
  = copied_map_walked snd ps tr res a0 a i0 idx;
    Seq.lemma_eq_intro a (CS.splice a0 i0 (i0 + Seq.length ps) (KM.values ps))

/// The empty trace starts a copy.
let copied_keys_empty (#k #v #b: Type0) (a0: Seq.seq k) (i0: int)
  : Lemma (requires 0 <= i0) (ensures copied_keys #k #v #b Seq.empty a0 a0 i0 i0)
  = ()

let copied_values_empty (#k #v #b: Type0) (a0: Seq.seq v) (i0: int)
  : Lemma (requires 0 <= i0) (ensures copied_values #k #v #b Seq.empty a0 a0 i0 i0)
  = ()

/// One more call, copying `f` of its pair at the cursor.
let copied_map_snoc (#k #v #b #u: Type0) (f: (k & v) -> u) (tr: Seq.seq (((k & v) & b) & bool))
    (a0 a: Seq.seq u) (i0 idx: int) (e: ((k & v) & b) & bool)
  : Lemma (requires copied_map f tr a0 a i0 idx /\ 0 <= idx /\ idx < Seq.length a /\ snd e == true)
          (ensures copied_map f (Seq.snoc tr e) a0 (Seq.upd a idx (f (tkey e))) i0 (idx + 1))
  = let tr' = Seq.snoc tr e in
    assert (forall (n: nat). n < Seq.length tr ==> Seq.index tr' n == Seq.index tr n);
    assert (Seq.index tr' (Seq.length tr) == e)

let copied_keys_snoc (#k #v #b: Type0) (tr: Seq.seq (((k & v) & b) & bool))
    (a0 a: Seq.seq k) (i0 idx: int) (e: ((k & v) & b) & bool)
  : Lemma (requires copied_keys tr a0 a i0 idx /\ 0 <= idx /\ idx < Seq.length a /\ snd e == true)
          (ensures copied_keys (Seq.snoc tr e) a0 (Seq.upd a idx (fst (tkey e))) i0 (idx + 1))
          [SMTPat (copied_keys (Seq.snoc tr e) a0 (Seq.upd a idx (fst (tkey e))) i0 (idx + 1))]
  = copied_map_snoc fst tr a0 a i0 idx e

let copied_values_snoc (#k #v #b: Type0) (tr: Seq.seq (((k & v) & b) & bool))
    (a0 a: Seq.seq v) (i0 idx: int) (e: ((k & v) & b) & bool)
  : Lemma (requires copied_values tr a0 a i0 idx /\ 0 <= idx /\ idx < Seq.length a /\ snd e == true)
          (ensures copied_values (Seq.snoc tr e) a0 (Seq.upd a idx (snd (tkey e))) i0 (idx + 1))
          [SMTPat (copied_values (Seq.snoc tr e) a0 (Seq.upd a idx (snd (tkey e))) i0 (idx + 1))]
  = copied_map_snoc snd tr a0 a i0 idx e
