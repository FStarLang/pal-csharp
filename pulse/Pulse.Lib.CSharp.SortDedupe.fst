module Pulse.Lib.CSharp.SortDedupe

/// R34.27. What `SortedSet<T>(IEnumerable<T>, IComparer<T>)` does with the items of a
/// collection whose comparer is not the set's: sort them, then keep the first of each run
/// of equivalent items. The result is determined only up to the comparer (the sort is not
/// stable), so it is specified by `set_of`: strictly sorted, every item of the source has an
/// equivalent in it, and each of its items is an item of the source. Verified, no admits;
/// the only trusted facts are the comparer axioms of `Order` (R22.30).

open Pulse.Lib.CSharp.Sort

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module SD = Pulse.Lib.CSharp.Sorted

/// `x` is an item of `s`.
let occurs_in (#t: Type) (s: Seq.seq t) (x: t) : prop =
  exists (j: nat). j < Seq.length s /\ Seq.index s j == x

/// Some item of `s[lo, hi)` is equivalent to `x` under `c`.
let equiv_in (#t: Type) (c: O.comparer t) (s: Seq.seq t) (x: t) (lo hi: nat) : prop =
  exists (k: nat). lo <= k /\ k < hi /\ k < Seq.length s /\ O.compare c x (Seq.index s k) == 0

let set_body (#t: Type) (c: O.comparer t) (items src: Seq.seq t) : prop =
  (forall (j: nat). j < Seq.length src ==> equiv_in c items (Seq.index src j) 0 (Seq.length items)) /\
  (forall (k: nat). k < Seq.length items ==> occurs_in src (Seq.index items k))

[@@"opaque_to_smt"]
let set_core (#t: Type) (c: O.comparer t) (items src: Seq.seq t) : prop = set_body c items src

let set_core_iff (#t: Type) (c: O.comparer t) (items src: Seq.seq t)
  : Lemma (set_core c items src <==> set_body c items src)
  = reveal_opaque (`%set_core) (set_core #t)

/// `SpecSortDedupe.SetOf(c, items, src)`: `items` is the set of `src`'s items under `c`.
/// Its quantified part is opaque to SMT (`set_core_iff` reveals it), so that a caller's
/// proof is not swamped by it.
let set_of (#t: Type) (c: O.comparer t) (items src: Seq.seq t) : prop =
  SD.strictly_sorted c items /\ set_core c items src

/// No items are the set of no items (the constructor's empty case).
let set_of_empty (#t: Type) (c: O.comparer t) (items src: Seq.seq t)
  : Lemma (requires Seq.length items == 0 /\ Seq.length src == 0)
          (ensures set_of c items src)
          [SMTPat (set_of c items src)]
  = set_core_iff c items src

/// `SpecSortDedupe.ComparerEquals(c, d)`: `c.Equals(d)` (R27.47), nothing more.
let comparer_equals (#t: Type) (c d: O.comparer t) : bool =
  Pulse.Lib.CSharp.ComparerIdentity.equals c (Pulse.Lib.CSharp.Obj.box d)

(* ------------------------------------------------------------------------- *)
(* A bijection on [0, n) is onto                                              *)
(* ------------------------------------------------------------------------- *)

let bij_onto (n: nat) (f: nat -> nat) (j: nat)
  : Lemma (requires is_bij n f /\ j < n)
          (ensures exists (i: nat). i < n /\ f i == j)
  = let open FStar.Classical in
    if FStar.IndefiniteDescription.strong_excluded_middle (exists (i: nat). i < n /\ f i == j) then ()
    else begin
      // `f` maps n positions into the n - 1 values other than j.
      let g (i: FStar.Fin.under n) : FStar.Fin.under (n - 1) =
        let v = f i in if v < j then v else v - 1 in
      let s : Seq.seq (FStar.Fin.under (n - 1)) = Seq.init n g in
      let (i1, i2) = FStar.Fin.pigeonhole #(n - 1) s in
      assert (Seq.index s i1 == g i1 /\ Seq.index s i2 == g i2);
      assert (f i1 == f i2)
    end

let permutation_onto (#t: Type) (a b: Seq.seq t) (j: nat)
  : Lemma (requires permutation a b /\ j < Seq.length a)
          (ensures exists (i: nat). i < Seq.length b /\ Seq.index b i == Seq.index a j)
  = reveal_opaque (`%permutation) (permutation #t);
    eliminate exists (f: nat -> nat). is_bij (Seq.length a) f /\
        (forall (i: nat). i < Seq.length a ==> Seq.index b i == Seq.index a (f i))
    with bij_onto (Seq.length a) f j

let permutation_into (#t: Type) (a b: Seq.seq t) (i: nat)
  : Lemma (requires permutation a b /\ i < Seq.length b)
          (ensures occurs_in a (Seq.index b i))
  = reveal_opaque (`%permutation) (permutation #t)

(* ------------------------------------------------------------------------- *)
(* The dedupe loop                                                            *)
(* ------------------------------------------------------------------------- *)

/// The loop `for (i = 1; i < n; i++) if (c(a[i], a[i-1]) != 0) a[index++] = a[i];` after
/// `i` items: `a[0, index)` is the set of the items so far, `a[i-1, n)` still sorted, and
/// every item of `src` has an equivalent kept or still to come.
let dedupe_body (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (i index n: int) : prop =
  1 <= index /\ index <= i /\ i <= n /\ n <= Seq.length a /\
  SD.strictly_sorted c (Seq.slice a 0 index) /\
  sorted_in c a (i - 1) n /\
  O.compare c (Seq.index a (index - 1)) (Seq.index a (i - 1)) == 0 /\
  (forall (j: nat). j < Seq.length src ==>
     equiv_in c a (Seq.index src j) 0 index \/ equiv_in c a (Seq.index src j) i n) /\
  (forall (k: nat). k < index ==> occurs_in src (Seq.index a k)) /\
  (forall (m: nat). i <= m /\ m < n ==> occurs_in src (Seq.index a m))

[@@"opaque_to_smt"]
let dedupe_core (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (i index n: int) : prop =
  dedupe_body c src a i index n

let core_iff (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (i index n: int)
  : Lemma (dedupe_core c src a i index n <==> dedupe_body c src a i index n)
  = reveal_opaque (`%dedupe_core) (dedupe_core #t)

/// Opaque to SMT but for its bounds, so that a caller's proof is not swamped by the
/// quantifiers (the lemmas below reveal it).
let dedupe_inv (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (i index n: int) : prop =
  1 <= index /\ index <= i /\ i <= n /\ n <= Seq.length a /\ dedupe_core c src a i index n

let dedupe_init (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (n: int)
  : Lemma (requires 1 <= n /\ n <= Seq.length a /\ permutation src (Seq.slice a 0 n) /\
                    sorted_in c a 0 n)
          (ensures dedupe_inv c src a 1 1 n)
  = core_iff c src a 1 1 n;
    let b = Seq.slice a 0 n in
    let cover (j: nat)
      : Lemma (j < Seq.length src ==> equiv_in c a (Seq.index src j) 0 1 \/ equiv_in c a (Seq.index src j) 1 n) =
      if j < Seq.length src then begin
        permutation_onto src b j;
        eliminate exists (i: nat). i < Seq.length b /\ Seq.index b i == Seq.index src j
        with O.compare_refl c (Seq.index a i)
      end in
    let into (k: nat) : Lemma (k < n ==> occurs_in src (Seq.index a k)) =
      if k < n then permutation_into src b k in
    FStar.Classical.forall_intro cover;
    FStar.Classical.forall_intro into;
    assert (Seq.length (Seq.slice a 0 1) == 1)

/// Appending an item greater than the last of a strictly sorted prefix keeps it so.
let keep_strict (#t: Type) (c: O.comparer t) (a: Seq.seq t) (index: nat) (x: t)
  : Lemma (requires 1 <= index /\ index < Seq.length a /\ SD.strictly_sorted c (Seq.slice a 0 index) /\
                    O.compare c (Seq.index a (index - 1)) x < 0)
          (ensures SD.strictly_sorted c (Seq.slice (Seq.upd a index x) 0 (index + 1)))
  = let p0 = Seq.slice a 0 index in
    let p1 = Seq.slice (Seq.upd a index x) 0 (index + 1) in
    let strict (p q: nat) : Lemma (p < q /\ q < index + 1 ==> O.compare c (Seq.index p1 p) (Seq.index p1 q) < 0) =
      if p < q && q < index + 1 then begin
        assert (Seq.index p1 p == Seq.index p0 p);
        if q < index then assert (Seq.index p1 q == Seq.index p0 q)
        else begin
          assert (Seq.index p1 q == x);
          if p < index - 1 then begin
            assert (O.compare c (Seq.index p0 p) (Seq.index p0 (index - 1)) < 0);
            O.compare_trans c (Seq.index p0 p) (Seq.index a (index - 1)) x
          end
        end
      end in
    FStar.Classical.forall_intro_2 strict

#push-options "--z3rlimit 80"
let dedupe_keep (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (i index n: int)
  : Lemma (requires dedupe_inv c src a i index n /\ i < n /\
                    O.compare c (Seq.index a i) (Seq.index a (i - 1)) <> 0)
          (ensures dedupe_inv c src (Seq.upd a index (Seq.index a i)) (i + 1) (index + 1) n)
  = core_iff c src a i index n;
    core_iff c src (Seq.upd a index (Seq.index a i)) (i + 1) (index + 1) n;
    let x = Seq.index a i in
    let a' = Seq.upd a index x in
    // a[index-1] ~ a[i-1] < a[i]
    assert (O.compare c (Seq.index a (i - 1)) x <= 0);
    O.compare_trans c (Seq.index a (index - 1)) (Seq.index a (i - 1)) x;
    keep_strict c a index x;
    let p1 = Seq.slice a' 0 (index + 1) in
    let cover (j: nat)
      : Lemma (j < Seq.length src ==>
               equiv_in c a' (Seq.index src j) 0 (index + 1) \/ equiv_in c a' (Seq.index src j) (i + 1) n) =
      if j < Seq.length src then begin
        let y = Seq.index src j in
        if FStar.IndefiniteDescription.strong_excluded_middle (equiv_in c a y 0 index) then
          eliminate exists (k: nat). 0 <= k /\ k < index /\ k < Seq.length a /\ O.compare c y (Seq.index a k) == 0
          with assert (Seq.index a' k == Seq.index a k)
        else
          eliminate exists (m: nat). i <= m /\ m < n /\ m < Seq.length a /\ O.compare c y (Seq.index a m) == 0
          with (if m = i then assert (Seq.index a' index == x)
                   else assert (Seq.index a' m == Seq.index a m))
      end in
    FStar.Classical.forall_intro cover;
    let into (k: nat) : Lemma (k < index + 1 ==> occurs_in src (Seq.index a' k)) =
      if k < index then assert (Seq.index a' k == Seq.index a k)
      else if k = index then assert (Seq.index a' k == Seq.index a i) in
    FStar.Classical.forall_intro into;
    let later (m: nat) : Lemma (i + 1 <= m /\ m < n ==> occurs_in src (Seq.index a' m)) =
      if i + 1 <= m && m < n then assert (Seq.index a' m == Seq.index a m) in
    FStar.Classical.forall_intro later;
    assert (Seq.index a' i == x);
    assert (Seq.index a' index == x);
    let still (p q: nat) : Lemma (i <= p /\ p <= q /\ q < n ==> O.compare c (Seq.index a' p) (Seq.index a' q) <= 0) =
      if i <= p && p <= q && q < n then
        assert (Seq.index a' p == Seq.index a p /\ Seq.index a' q == Seq.index a q) in
    FStar.Classical.forall_intro_2 still;
    assert (SD.strictly_sorted c p1);
    assert (sorted_in c a' i n);
    assert (O.compare c (Seq.index a' index) (Seq.index a' i) == 0)

#pop-options

let dedupe_skip (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (i index n: int)
  : Lemma (requires dedupe_inv c src a i index n /\ i < n /\
                    O.compare c (Seq.index a i) (Seq.index a (i - 1)) == 0)
          (ensures dedupe_inv c src a (i + 1) index n)
  = core_iff c src a i index n;
    let x = Seq.index a i in
    let last = Seq.index a (index - 1) in
    O.compare_trans c last (Seq.index a (i - 1)) x;
    O.compare_trans c x (Seq.index a (i - 1)) last;
    let cover (j: nat)
      : Lemma (j < Seq.length src ==>
               equiv_in c a (Seq.index src j) 0 index \/ equiv_in c a (Seq.index src j) (i + 1) n) =
      if j < Seq.length src then begin
        let y = Seq.index src j in
        if FStar.IndefiniteDescription.strong_excluded_middle (equiv_in c a y 0 index) then ()
        else
          eliminate exists (m: nat). i <= m /\ m < n /\ m < Seq.length a /\ O.compare c y (Seq.index a m) == 0
          with (if m = i then begin
                     O.compare_trans c y x last;
                     O.compare_trans c last x y;
                     assert (O.compare c y (Seq.index a (index - 1)) == 0);
                     assert (equiv_in c a y 0 index)
                   end)
      end in
    FStar.Classical.forall_intro cover;
    let still (p q: nat) : Lemma (i <= p /\ p <= q /\ q < n ==> O.compare c (Seq.index a p) (Seq.index a q) <= 0) =
      () in
    FStar.Classical.forall_intro_2 still;
    assert (sorted_in c a i n);
    assert (O.compare c last x == 0);
    assert (1 <= index /\ index <= i + 1 /\ i + 1 <= n /\ n <= Seq.length a);
    assert (SD.strictly_sorted c (Seq.slice a 0 index));
    assert (sorted_in c a ((i + 1) - 1) n);
    assert (O.compare c (Seq.index a (index - 1)) (Seq.index a ((i + 1) - 1)) == 0);
    assert (forall (j: nat). j < Seq.length src ==>
     equiv_in c a (Seq.index src j) 0 index \/ equiv_in c a (Seq.index src j) (i + 1) n);
    assert (forall (k: nat). k < index ==> occurs_in src (Seq.index a k));
    assert (forall (m: nat). i + 1 <= m /\ m < n ==> occurs_in src (Seq.index a m));
    core_iff c src a (i + 1) index n

let dedupe_done (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (index n: int)
  : Lemma (requires dedupe_inv c src a n index n)
          (ensures set_of c (Seq.slice a 0 index) src)
  = core_iff c src a n index n;
    let p = Seq.slice a 0 index in
    assert (Seq.length p == index);
    let cover (j: nat) : Lemma (j < Seq.length src ==> equiv_in c p (Seq.index src j) 0 (Seq.length p)) =
      if j < Seq.length src then begin
        assert (equiv_in c a (Seq.index src j) 0 index);
        eliminate exists (k: nat). 0 <= k /\ k < index /\ k < Seq.length a /\ O.compare c (Seq.index src j) (Seq.index a k) == 0
        with assert (Seq.index p k == Seq.index a k)
      end in
    FStar.Classical.forall_intro cover;
    let into (k: nat) : Lemma (k < Seq.length p ==> occurs_in src (Seq.index p k)) =
      if k < Seq.length p then assert (Seq.index p k == Seq.index a k) in
    FStar.Classical.forall_intro into;
    set_core_iff c p src

/// A strictly sorted sequence is the set of its own items.
let set_of_self (#t: Type) (c: O.comparer t) (s: Seq.seq t)
  : Lemma (requires SD.strictly_sorted c s) (ensures set_of c s s)
  = let cover (j: nat) : Lemma (j < Seq.length s ==> equiv_in c s (Seq.index s j) 0 (Seq.length s)) =
      if j < Seq.length s then O.compare_refl c (Seq.index s j) in
    FStar.Classical.forall_intro cover;
    set_core_iff c s s

/// A snapshot of a collection's items (R34.26): `CopyTo` into a fresh array of its `Count`
/// overwrites the whole array.
let splice_whole (#t: Type0) (v: Seq.seq t) (i j: nat) (w: Seq.seq t)
  : Lemma (requires i == 0 /\ j == Seq.length v /\ Seq.length w == Seq.length v)
          (ensures  Pulse.Lib.CSharp.Seq.splice v i j w == w)
          [SMTPat (Pulse.Lib.CSharp.Seq.splice v i j w)]
  = Pulse.Lib.CSharp.Seq.splice_all v w

/// One step of the loop, either arm: what `dedupe_keep` and `dedupe_skip` give, stated
/// before the branch so that the join of its arms keeps it.
let dedupe_step (#t: Type) (c: O.comparer t) (src a: Seq.seq t) (i index n: int)
  : Lemma (requires dedupe_inv c src a i index n /\ i < n)
          (ensures (O.compare c (Seq.index a i) (Seq.index a (i - 1)) <> 0 ==>
                      dedupe_inv c src (Seq.upd a index (Seq.index a i)) (i + 1) (index + 1) n) /\
                   (O.compare c (Seq.index a i) (Seq.index a (i - 1)) == 0 ==>
                      dedupe_inv c src a (i + 1) index n))
  = if O.compare c (Seq.index a i) (Seq.index a (i - 1)) <> 0
    then dedupe_keep c src a i index n
    else dedupe_skip c src a i index n
