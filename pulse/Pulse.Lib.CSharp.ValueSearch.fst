module Pulse.Lib.CSharp.ValueSearch

/// R32.8. A search of a map's values: `SortedDictionary<K, V>.ContainsValue`, which walks its
/// pair set (R27.39) with a callback that stops at the first pair whose value matches.

module Seq = FStar.Seq
module RW = Pulse.Lib.CSharp.RegionWalk

/// `x` matches `y` as `ContainsValue` tests it: `x == null` when `y` is null, and
/// `EqualityComparer<V>.Default.Equals(x, y)` otherwise.
let value_matches (#v: Type0) (x y: v) : bool =
  if Pulse.Lib.CSharp.Sorted.is_null y then Pulse.Lib.CSharp.Sorted.is_null x
  else Pulse.Lib.CSharp.Bcl.default_equals x y

let rec find_value (#k #v: Type0) (s: Seq.seq (k & v)) (y: v) (i: nat { i <= Seq.length s })
  : Tot bool (decreases Seq.length s - i)
  = if i = Seq.length s then false
    else value_matches (snd (Seq.index s i)) y || find_value s y (i + 1)

/// Some pair of `s` has a value matching `y`.
let has_value (#k #v: Type0) (s: Seq.seq (k & v)) (y: v) : bool = find_value s y 0

let rec find_value_exists (#k #v: Type0) (s: Seq.seq (k & v)) (y: v) (i: nat { i <= Seq.length s })
  : Lemma (ensures find_value s y i <==>
                   (exists (j: nat). i <= j /\ j < Seq.length s /\ value_matches (snd (Seq.index s j)) y))
          (decreases Seq.length s - i)
  = if i = Seq.length s then () else find_value_exists s y (i + 1)

/// The protocol of the search's callback, called so far on the entries of `tr`: it returned
/// false exactly on a match, and `found` records whether there was one.
let searched (#k #v #b: Type0) (tr: Seq.seq (((k & v) & b) & bool)) (y: v) (found: bool) : prop =
  (forall (i: nat). i < Seq.length tr ==>
     snd (Seq.index tr i) == not (value_matches (snd (RW.tkey (Seq.index tr i))) y)) /\
  (found == true <==> (exists (i: nat). i < Seq.length tr /\ value_matches (snd (RW.tkey (Seq.index tr i))) y))

let searched_empty (#k #v #b: Type0) (y: v)
  : Lemma (searched #k #v #b Seq.empty y false)
          [SMTPat (searched #k #v #b Seq.empty y false)]
  = ()

/// One more call: it returns false and sets `found` on a match, and returns true otherwise.
let searched_snoc (#k #v #b: Type0) (tr: Seq.seq (((k & v) & b) & bool)) (y: v) (found found': bool)
    (e: ((k & v) & b) & bool)
  : Lemma (requires searched tr y found /\
                    snd e == not (value_matches (snd (RW.tkey e)) y) /\
                    found' == (found || value_matches (snd (RW.tkey e)) y))
          (ensures searched (Seq.snoc tr e) y found')
          [SMTPat (searched (Seq.snoc tr e) y found'); SMTPat (searched tr y found)]
  = let tr' = Seq.snoc tr e in
    assert (forall (i: nat). i < Seq.length tr ==> Seq.index tr' i == Seq.index tr i);
    assert (Seq.index tr' (Seq.length tr) == e)

/// A walk of every pair the search did not stop: `found` is whether any value matched.
let searched_walked (#k #v #b: Type0) (keys: Seq.seq (k & v)) (tr: Seq.seq (((k & v) & b) & bool))
    (res: bool) (y: v) (found: bool)
  : Lemma (requires RW.walked keys tr res /\ searched tr y found)
          (ensures found == has_value keys y)
          [SMTPat (RW.walked keys tr res); SMTPat (searched tr y found)]
  = find_value_exists keys y 0;
    if res then ()
    else assert (value_matches (snd (RW.tkey (Seq.index tr (Seq.length tr - 1)))) y)
