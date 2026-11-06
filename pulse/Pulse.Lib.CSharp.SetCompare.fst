module Pulse.Lib.CSharp.SetCompare

/// R27.49. Comparing two sequences position by position under a comparer: what
/// `SortedSet<T>.SetEquals` computes when it walks two sets of one comparer in step.
///
/// * `same_keys c s t`: `s` and `t` have the same length, and each pair of elements at the
///   same position compares equal under `c`.
/// * `same_keys_step`, `same_keys_whole`: the steps of a walk over suffixes.
/// * `same_keys_members`: on two strictly sorted sequences, `same_keys` is equality of the
///   sets they hold under `c` — every element of one compares equal to some element of the
///   other — which is what `SetEquals` means.
///
/// Everything is proved from `Pulse.Lib.CSharp.Order`'s axioms; nothing new is trusted.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted

let rec same_keys (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Tot bool (decreases Seq.length s) =
  if Seq.length s = 0 || Seq.length t = 0 then Seq.length s = Seq.length t
  else O.compare c (Seq.index s 0) (Seq.index t 0) = 0 && same_keys c (Seq.tail s) (Seq.tail t)

let same_keys_step (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires 0 <= i /\ i <= Seq.length s /\ 0 <= j /\ j <= Seq.length t)
          (ensures same_keys c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t)) ==
                   (if i = Seq.length s || j = Seq.length t then i = Seq.length s && j = Seq.length t
                    else O.compare c (Seq.index s i) (Seq.index t j) = 0 &&
                         same_keys c (Seq.slice s (i + 1) (Seq.length s)) (Seq.slice t (j + 1) (Seq.length t))))
  = if i = Seq.length s || j = Seq.length t then ()
    else begin
      Seq.lemma_eq_elim (Seq.tail (Seq.slice s i (Seq.length s))) (Seq.slice s (i + 1) (Seq.length s));
      Seq.lemma_eq_elim (Seq.tail (Seq.slice t j (Seq.length t))) (Seq.slice t (j + 1) (Seq.length t))
    end

let same_keys_whole (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (same_keys c (Seq.slice s 0 (Seq.length s)) (Seq.slice t 0 (Seq.length t)) == same_keys c s t)
  = Seq.lemma_eq_elim (Seq.slice s 0 (Seq.length s)) s;
    Seq.lemma_eq_elim (Seq.slice t 0 (Seq.length t)) t

/// Some element of `s` compares equal to `x`.
let has (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x: a) : prop =
  exists (i: nat). i < Seq.length s /\ O.compare c (Seq.index s i) x == 0

/// The sets `s` and `t` hold under `c` are equal.
let same_members (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) : prop =
  forall (x: a). has c s x <==> has c t x

let eq_trans (#a: Type0) (c: O.comparer a) (x y z: a)
  : Lemma (requires O.compare c x y == 0 /\ O.compare c y z == 0) (ensures O.compare c x z == 0)
  = O.compare_trans c x y z; O.compare_trans c z y x

let lt_eq (#a: Type0) (c: O.comparer a) (x y z: a)
  : Lemma (requires O.compare c x y < 0 /\ O.compare c y z == 0) (ensures O.compare c x z < 0)
  = O.compare_trans c x y z

let eq_lt (#a: Type0) (c: O.comparer a) (x y z: a)
  : Lemma (requires O.compare c x y == 0 /\ O.compare c y z < 0) (ensures O.compare c x z < 0)
  = O.compare_trans c x y z

/// Position by position.
let pointwise (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) : prop =
  Seq.length s == Seq.length t /\
  (forall (i: nat). i < Seq.length s ==> O.compare c (Seq.index s i) (Seq.index t i) == 0)

let rec same_keys_pointwise (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (ensures same_keys c s t <==> pointwise c s t) (decreases Seq.length s)
  = if Seq.length s = 0 || Seq.length t = 0 then ()
    else begin
      same_keys_pointwise c (Seq.tail s) (Seq.tail t);
      assert (forall (i: nat). 0 < i /\ i < Seq.length s ==> Seq.index (Seq.tail s) (i - 1) == Seq.index s i);
      assert (forall (i: nat). 0 < i /\ i < Seq.length t ==> Seq.index (Seq.tail t) (i - 1) == Seq.index t i)
    end

let pointwise_members (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires pointwise c s t) (ensures same_members c s t)
  = let aux (x: a) : Lemma (has c s x <==> has c t x) =
      let l (i: nat{i < Seq.length s}) : Lemma
          ((O.compare c (Seq.index s i) x == 0 ==> O.compare c (Seq.index t i) x == 0) /\
           (O.compare c (Seq.index t i) x == 0 ==> O.compare c (Seq.index s i) x == 0))
        = if O.compare c (Seq.index s i) x = 0 then eq_trans c (Seq.index t i) (Seq.index s i) x;
          if O.compare c (Seq.index t i) x = 0 then eq_trans c (Seq.index s i) (Seq.index t i) x
      in
      FStar.Classical.forall_intro l
    in
    FStar.Classical.forall_intro aux

let witness (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x: a)
  : Ghost nat (requires has c s x)
              (ensures fun i -> i < Seq.length s /\ O.compare c (Seq.index s i) x == 0)
  = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < Seq.length s /\ O.compare c (Seq.index s i) x == 0)

let tail_sorted (#a: Type0) (c: O.comparer a) (s: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ Seq.length s > 0) (ensures S.strictly_sorted c (Seq.tail s))
  = assert (forall (i: nat). i < Seq.length s - 1 ==> Seq.index (Seq.tail s) i == Seq.index s (i + 1))

/// What a tail of one holds, the tail of the other holds, once the heads agree.
let tail_has (#a: Type0) (c: O.comparer a) (p q: Seq.seq a) (x: a)
  : Lemma (requires S.strictly_sorted c p /\ S.strictly_sorted c q /\ same_members c p q /\
                    Seq.length p > 0 /\ Seq.length q > 0 /\
                    O.compare c (Seq.index p 0) (Seq.index q 0) == 0 /\ has c (Seq.tail p) x)
          (ensures has c (Seq.tail q) x)
  = let i = witness c (Seq.tail p) x in
    let pi : a = Seq.index p (i + 1) in
    assert (Seq.index (Seq.tail p) i == pi);
    assert (has c p x);
    let j = witness c q x in
    if j = 0 then begin
      eq_trans c (Seq.index p 0) (Seq.index q 0) x;
      O.compare_antisym c pi x;
      eq_trans c (Seq.index p 0) x pi;
      assert (O.compare c (Seq.index p 0) pi < 0)
    end else begin
      let j' : nat = j - 1 in
      assert (Seq.index (Seq.tail q) j' == Seq.index q j)
    end

/// Two strictly sorted sequences holding the same set agree at their heads, and their
/// tails hold the same set.
let heads_members (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t /\ same_members c s t /\
                    Seq.length s > 0 /\ Seq.length t > 0)
          (ensures O.compare c (Seq.index s 0) (Seq.index t 0) == 0 /\
                   same_members c (Seq.tail s) (Seq.tail t))
  = let s0 = Seq.index s 0 in
    let t0 = Seq.index t 0 in
    assert (has c s s0);
    let k = witness c t s0 in
    assert (has c t t0);
    let m = witness c s t0 in
    if k > 0 then begin
      lt_eq c t0 (Seq.index t k) s0;
      if m > 0 then begin
        eq_lt c (Seq.index s m) t0 s0;
        O.compare_antisym c s0 (Seq.index s m)
      end else ()
    end;
    let both (x: a) : Lemma (has c (Seq.tail s) x <==> has c (Seq.tail t) x) =
      O.compare_antisym c s0 t0;
      FStar.Classical.move_requires (tail_has c s t) x;
      FStar.Classical.move_requires (tail_has c t s) x
    in
    FStar.Classical.forall_intro both

let rec members_pointwise (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t /\ same_members c s t)
          (ensures pointwise c s t) (decreases Seq.length s)
  = if Seq.length s = 0 && Seq.length t = 0 then ()
    else if Seq.length s = 0 then (assert (has c t (Seq.index t 0)))
    else if Seq.length t = 0 then (assert (has c s (Seq.index s 0)))
    else begin
      heads_members c s t;
      tail_sorted c s; tail_sorted c t;
      members_pointwise c (Seq.tail s) (Seq.tail t);
      assert (forall (i: nat). 0 < i /\ i < Seq.length s ==> Seq.index (Seq.tail s) (i - 1) == Seq.index s i);
      assert (forall (i: nat). 0 < i /\ i < Seq.length t ==> Seq.index (Seq.tail t) (i - 1) == Seq.index t i)
    end

/// On strictly sorted sequences, `same_keys` is equality of the sets they hold under `c`.
let same_keys_members (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t)
          (ensures same_keys c s t <==> same_members c s t)
  = same_keys_pointwise c s t;
    FStar.Classical.move_requires (pointwise_members c s) t;
    FStar.Classical.move_requires (members_pointwise c s) t
