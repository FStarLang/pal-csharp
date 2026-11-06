module Pulse.Lib.CSharp.Sorted
#lang-pulse

/// Sorted sequences, and `Array.BinarySearch` under a comparer (doc/translation.md §25).
///
/// Everything here is proved from `Pulse.Lib.CSharp.Order`'s total-preorder axioms, except
/// `is_null`, which is a MODELING AXIOM (R25.4).

open Pulse
open Pulse.Lib.CSharp.Array
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module I32 = FStar.Int32
module O = Pulse.Lib.CSharp.Order

/// MODELING AXIOM (R25.4), stated in `Pulse.Lib.CSharp.Null`.
let is_null (#t: Type) (x: t) : bool = Pulse.Lib.CSharp.Null.is_null x

/// R25.5. `c ?? Comparer<T>.Default`: what a BCL search does with the comparer it is given.
let or_default (#t: Type) (c: O.comparer t) : O.comparer t =
  if is_null c then O.default_comparer t else c

/// R25.5. The complement of a negative `int`, the position a missed search encodes.
let lognot_negative (x: int{FStar.Int.size x 32 /\ x < 0})
  : Lemma (FStar.Int.lognot #32 x == - x - 1)
          [SMTPat (FStar.Int.lognot #32 x)]
  = FStar.Int.lognot_negative #32 x;
    FStar.UInt.lemma_lognot_value_mod #32 (x + pow2 32)

let lognot_negative_i32 (x: I32.t{I32.v x < 0})
  : Lemma (I32.v (I32.lognot x) == - (I32.v x) - 1)
          [SMTPat (I32.lognot x)]
  = lognot_negative (I32.v x)

/// `c.Compare(x, y)`, as the `int` a program reads: its sign is the model's.
let compare_i32 (#t: Type) (c: O.comparer t) (x y: t) : I32.t =
  if O.compare c x y < 0 then (-1l) else if O.compare c x y = 0 then 0l else 1l

/// `s` is in order: each element is at most every later one.
let sorted (#t: Type) (c: O.comparer t) (s: Seq.seq t) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==>
    O.compare c (Seq.index s i) (Seq.index s j) <= 0

/// `s` is in strict order: each element is less than every later one, so no two are equal.
let strictly_sorted (#t: Type) (c: O.comparer t) (s: Seq.seq t) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==>
    O.compare c (Seq.index s i) (Seq.index s j) < 0

/// The number of elements of `s` less than `x`: where `x` goes in a sorted `s`.
let rec lower_bound (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t)
  : Tot nat (decreases Seq.length s)
  = if Seq.length s = 0 then 0
    else (if O.compare c (Seq.head s) x < 0 then 1 else 0) + lower_bound c (Seq.tail s) x

let rec lower_bound_le (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t)
  : Lemma (ensures lower_bound c s x <= Seq.length s)
          (decreases Seq.length s)
          [SMTPat (lower_bound c s x)]
  = if Seq.length s = 0 then () else lower_bound_le c (Seq.tail s) x

/// R25.6. The position of an element equivalent to `x` in a strictly sorted `s`, or -1:
/// where `x` would go, if what is there is equivalent to it.
let key_index (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) : int =
  let lb = lower_bound c s x in
  if lb < Seq.length s && O.compare c (Seq.index s lb) x = 0 then lb else -1

/// The BCL's binary search over `[lo, hi]` (inclusive bounds), step for step:
/// `ArraySortHelper<T>.InternalBinarySearch`. `-lo - 1` is `~lo`.
let rec bsearch (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (lo hi: int)
  : Tot int (decreases (if hi >= lo then hi - lo + 1 else 0))
  = if lo > hi || lo < 0 || hi >= Seq.length s then -lo - 1
    else
      let i = lo + (hi - lo) / 2 in
      let o = O.compare c (Seq.index s i) x in
      if o = 0 then i
      else if o < 0 then bsearch c s x (i + 1) hi
      else bsearch c s x lo (i - 1)

/// `Array.BinarySearch(a, index, length, x, c)` on contents `s`.
let range_search (#t: Type) (c: O.comparer t) (s: Seq.seq t) (index length: int) (x: t) : int =
  bsearch c s x index (index + length - 1)

(* ---- what a search finds ---- *)

let rec bsearch_bounds (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (lo hi: int)
  : Lemma (requires 0 <= lo /\ lo <= hi + 1 /\ hi < Seq.length s)
          (ensures (let r = bsearch c s x lo hi in
                    (r >= 0 ==> lo <= r /\ r <= hi /\ O.compare c (Seq.index s r) x == 0) /\
                    (r < 0 ==> lo <= -r - 1 /\ -r - 1 <= hi + 1)))
          (decreases (if hi >= lo then hi - lo + 1 else 0))
  = if lo > hi then ()
    else
      let i = lo + (hi - lo) / 2 in
      let o = O.compare c (Seq.index s i) x in
      if o = 0 then ()
      else if o < 0 then bsearch_bounds c s x (i + 1) hi
      else bsearch_bounds c s x lo (i - 1)

/// In a sorted range, a miss partitions it: everything before `~r` is less than `x`,
/// everything from `~r` on is greater.
let below (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (a b: int) : prop =
  forall (k: nat). a <= k /\ k < b /\ k < Seq.length s ==> O.compare c (Seq.index s k) x < 0

let above (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (a b: int) : prop =
  forall (k: nat). a <= k /\ k < b /\ k < Seq.length s ==> O.compare c (Seq.index s k) x > 0

let sorted_between (#t: Type) (c: O.comparer t) (s: Seq.seq t) (a b: int) : prop =
  forall (i j: nat). a <= i /\ i < j /\ j < b /\ j < Seq.length s ==>
    O.compare c (Seq.index s i) (Seq.index s j) <= 0

let below_extend (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (a lo i: nat)
  : Lemma (requires sorted_between c s a (i + 1) /\ i < Seq.length s /\ a <= lo /\ lo <= i /\
                    below c s x a lo /\ O.compare c (Seq.index s i) x < 0)
          (ensures below c s x a (i + 1))
  = let aux (k: nat{k < Seq.length s}) : Lemma (requires lo <= k /\ k < i) (ensures O.compare c (Seq.index s k) x < 0)
      = O.compare_trans c (Seq.index s k) (Seq.index s i) x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let above_extend (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (i hi b: nat)
  : Lemma (requires sorted_between c s i b /\ i <= hi /\ hi < b /\ b <= Seq.length s /\
                    above c s x (hi + 1) b /\ O.compare c (Seq.index s i) x > 0)
          (ensures above c s x i b)
  = let aux (k: nat{k < Seq.length s}) : Lemma (requires i < k /\ k <= hi) (ensures O.compare c (Seq.index s k) x > 0)
      = O.compare_antisym c (Seq.index s i) x;
        O.compare_trans c x (Seq.index s i) (Seq.index s k);
        O.compare_antisym c x (Seq.index s k)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let rec bsearch_miss (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (a b lo hi: int)
  : Lemma (requires 0 <= a /\ a <= lo /\ lo <= hi + 1 /\ hi + 1 <= b /\ b <= Seq.length s /\
                    sorted_between c s a b /\ below c s x a lo /\ above c s x (hi + 1) b /\
                    bsearch c s x lo hi < 0)
          (ensures (let p = -(bsearch c s x lo hi) - 1 in below c s x a p /\ above c s x p b))
          (decreases (if hi >= lo then hi - lo + 1 else 0))
  = if lo > hi then ()
    else
      let i = lo + (hi - lo) / 2 in
      let o = O.compare c (Seq.index s i) x in
      if o = 0 then ()
      else if o < 0 then (below_extend c s x a lo i; bsearch_miss c s x a b (i + 1) hi)
      else (above_extend c s x i hi b; bsearch_miss c s x a b lo (i - 1))

let sorted_slice (#t: Type) (c: O.comparer t) (s: Seq.seq t) (a b: nat)
  : Lemma (requires a <= b /\ b <= Seq.length s /\ sorted c (Seq.slice s a b))
          (ensures sorted_between c s a b)
  = let aux (i: nat{i < Seq.length s}) (j: nat{j < Seq.length s}) : Lemma (requires a <= i /\ i < j /\ j < b)
                               (ensures O.compare c (Seq.index s i) (Seq.index s j) <= 0)
      = assert (Seq.index (Seq.slice s a b) (i - a) == Seq.index s i);
        assert (Seq.index (Seq.slice s a b) (j - a) == Seq.index s j)
    in
    FStar.Classical.forall_intro_2 (fun i j -> FStar.Classical.move_requires (aux i) j)

let strictly_sorted_sorted (#t: Type) (c: O.comparer t) (s: Seq.seq t)
  : Lemma (requires strictly_sorted c s) (ensures sorted c s)
          [SMTPat (strictly_sorted c s)]
  = ()

/// The number of elements below `x` in a sequence whose elements below `x` are its
/// first `p`.
/// Removing one element keeps a sequence strictly sorted.
let strictly_sorted_remove (#t: Type) (c: O.comparer t) (s: Seq.seq t) (i n: nat)
  : Lemma (requires strictly_sorted c s /\ i < n /\ n == Seq.length s)
          (ensures strictly_sorted c (Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) n)))
          [SMTPat (strictly_sorted c (Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) n)))]
  = let r = Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) n) in
    let f (k: nat{k < Seq.length r}) : nat = if k < i then k else k + 1 in
    assert (forall (k: nat). k < Seq.length r ==> Seq.index r k == Seq.index s (f k))

let rec lower_bound_prefix (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (p: nat)
  : Lemma (requires p <= Seq.length s /\
                    (forall (k: nat). k < p ==> O.compare c (Seq.index s k) x < 0) /\
                    (forall (k: nat). p <= k /\ k < Seq.length s ==> O.compare c (Seq.index s k) x >= 0))
          (ensures lower_bound c s x == p)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if p = 0 then lower_bound_prefix c (Seq.tail s) x 0
    else lower_bound_prefix c (Seq.tail s) x (p - 1)

let range_search_miss (#t: Type) (c: O.comparer t) (s: Seq.seq t) (index length: nat) (x: t)
  : Lemma (requires index + length <= Seq.length s /\
                    sorted c (Seq.slice s index (index + length)) /\
                    range_search c s index length x < 0)
          (ensures (let r = range_search c s index length x in
              (forall (k: nat). index <= k /\ k < -r - 1 /\ k < Seq.length s ==> O.compare c (Seq.index s k) x < 0) /\
              (forall (k: nat). -r - 1 <= k /\ k < index + length /\ k < Seq.length s ==> O.compare c (Seq.index s k) x > 0) /\
              -r - 1 == index + lower_bound c (Seq.slice s index (index + length)) x))
  = let r = range_search c s index length x in
    bsearch_bounds c s x index (index + length - 1);
    sorted_slice c s index (index + length);
    bsearch_miss c s x index (index + length) index (index + length - 1);
    let w = Seq.slice s index (index + length) in
    let p = -r - 1 - index in
    assert (forall (k: nat). k < Seq.length w ==> Seq.index w k == Seq.index s (index + k));
    lower_bound_prefix c w x p

let range_search_hit (#t: Type) (c: O.comparer t) (s: Seq.seq t) (index length: nat) (x: t)
  : Lemma (requires index + length <= Seq.length s /\
                    strictly_sorted c (Seq.slice s index (index + length)) /\
                    range_search c s index length x >= 0)
          (ensures (let r = range_search c s index length x in
              (forall (k: nat). index <= k /\ k < index + length /\ k < Seq.length s /\ k <> r ==>
                 O.compare c (Seq.index s k) x <> 0) /\
              r == index + lower_bound c (Seq.slice s index (index + length)) x))
  = let r = range_search c s index length x in
    bsearch_bounds c s x index (index + length - 1);
    let w = Seq.slice s index (index + length) in
    let aux (k: nat{k < Seq.length s}) : Lemma (requires index <= k /\ k < index + length /\ k <> r)
                             (ensures (k < r ==> O.compare c (Seq.index s k) x < 0) /\
                                      (k > r ==> O.compare c (Seq.index s k) x > 0))
      = assert (Seq.index w (k - index) == Seq.index s k);
        assert (Seq.index w (r - index) == Seq.index s r);
        O.compare_antisym c (Seq.index s r) x;
        if k < r then O.compare_trans c (Seq.index s k) (Seq.index s r) x
        else (O.compare_antisym c (Seq.index s r) (Seq.index s k);
              O.compare_trans c x (Seq.index s r) (Seq.index s k);
              O.compare_antisym c x (Seq.index s k))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    assert (forall (k: nat). k < Seq.length w ==> Seq.index w k == Seq.index s (index + k));
    lower_bound_prefix c w x (r - index)

/// What `Array.BinarySearch` returns, as a contract can use it.
let range_search_spec (#t: Type) (c: O.comparer t) (s: Seq.seq t) (index length: int) (x: t)
  : Lemma (requires 0 <= index /\ 0 <= length /\ index + length <= Seq.length s)
          (ensures (let r = range_search c s index length x in
            (r >= 0 ==> index <= r /\ r < index + length /\ O.compare c (Seq.index s r) x == 0) /\
            (r < 0 ==> index <= -r - 1 /\ -r - 1 <= index + length) /\
            (sorted c (Seq.slice s index (index + length)) /\ r < 0 ==>
              (forall (k: nat). index <= k /\ k < -r - 1 /\ k < Seq.length s ==> O.compare c (Seq.index s k) x < 0) /\
              (forall (k: nat). -r - 1 <= k /\ k < index + length /\ k < Seq.length s ==> O.compare c (Seq.index s k) x > 0) /\
              -r - 1 == index + lower_bound c (Seq.slice s index (index + length)) x) /\
            (strictly_sorted c (Seq.slice s index (index + length)) /\ r >= 0 ==>
              (forall (k: nat). index <= k /\ k < index + length /\ k < Seq.length s /\ k <> r ==>
                 O.compare c (Seq.index s k) x <> 0) /\
              r == index + lower_bound c (Seq.slice s index (index + length)) x)))
          [SMTPat (range_search c s index length x)]
  = bsearch_bounds c s x index (index + length - 1);
    FStar.Classical.move_requires (range_search_miss c s index length) x;
    FStar.Classical.move_requires (range_search_hit c s index length) x

(* ---- the program ---- *)

/// `Array.BinarySearch<T>(a, index, length, x, c)` (R25.5). The BCL's argument checks
/// are the precondition (R22.25); the result is `range_search`, whatever the order of
/// `a` -- a sorted range is what makes it mean something (`range_search_spec`).
fn range_search_array (#t: Type0) (a: array t) (index length: I32.t) (x: t) (c: O.comparer t)
  (#p: perm)
  (#s: Ghost.erased (Seq.seq t) {
     I32.v index >= 0 /\ I32.v length >= 0 /\ I32.v index + I32.v length <= Seq.length s })
  preserves A.pts_to a #p s
  returns  r: I32.t
  ensures  pure (I32.v r == range_search c s (I32.v index) (I32.v length) x)
{
  A.pts_to_len a;
  let mut lo = index;
  let mut hi = I32.sub (I32.add index length) 1l;
  let mut r = (-1l);
  while (I32.lte !lo !hi)
  invariant exists* vlo vhi vr.
    pts_to lo vlo ** pts_to hi vhi ** pts_to r vr ** A.pts_to a #p s **
    pure (I32.v index <= I32.v vlo /\ I32.v vlo <= I32.v vhi + 1 /\
          I32.v vhi < I32.v index + I32.v length /\
          (if I32.v vr >= 0
           then I32.v vlo > I32.v vhi /\
                I32.v vr == range_search c s (I32.v index) (I32.v length) x
           else I32.v vr == -1 /\
                bsearch c s x (I32.v vlo) (I32.v vhi) ==
                range_search c s (I32.v index) (I32.v length) x))
  decreases (I32.v !hi - I32.v !lo + 1)
  {
    let vlo = !lo;
    let vhi = !hi;
    let i = I32.add vlo (I32.div (I32.sub vhi vlo) 2l);
    let y = read a i;
    let o = compare_i32 c y x;
    if (o = 0l) { r := i; hi := I32.sub vlo 1l }
    else if (I32.lt o 0l) { lo := I32.add i 1l }
    else { hi := I32.sub i 1l }
  };
  let vr = !r;
  if (I32.gte vr 0l) { vr } else { I32.sub (I32.sub 0l !lo) 1l }
}
