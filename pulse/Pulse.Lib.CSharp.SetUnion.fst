module Pulse.Lib.CSharp.SetUnion

/// The union of two strictly sorted sets, as `SortedSet<T>.UnionWith` builds it, two ways.
///
/// * `union c s t` is the merge: the two sequences interleaved in order, and of two elements
///   that compare equal, the one of `t`.
/// * `add_all c s t` adds the elements of `t` to `s` one by one, first to last, skipping
///   those already members: of two elements that compare equal, the one of `s` stays.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module I = Pulse.Lib.CSharp.SetInter
module TH = Pulse.Lib.CSharp.TopDownHeap

let rec union (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Tot (Seq.seq a) (decreases Seq.length s + Seq.length t) =
  if Seq.length s = 0 then t
  else if Seq.length t = 0 then s
  else
    let o = O.compare c (Seq.head s) (Seq.head t) in
    if o < 0 then Seq.cons (Seq.head s) (union c (Seq.tail s) t)
    else if o = 0 then Seq.cons (Seq.head t) (union c (Seq.tail s) (Seq.tail t))
    else Seq.cons (Seq.head t) (union c s (Seq.tail t))

/// One step of the merge: the suffixes from `i` in `s` and `j` in `t`.
let union_step (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires 0 <= i /\ i < Seq.length s /\ 0 <= j /\ j < Seq.length t)
          (ensures (let si = Seq.slice s i (Seq.length s) in
                    let tj = Seq.slice t j (Seq.length t) in
                    let si' = Seq.slice s (i + 1) (Seq.length s) in
                    let tj' = Seq.slice t (j + 1) (Seq.length t) in
                    let o = O.compare c (Seq.index s i) (Seq.index t j) in
                    union c si tj ==
                    (if o < 0 then Seq.cons (Seq.index s i) (union c si' tj)
                     else if o = 0 then Seq.cons (Seq.index t j) (union c si' tj')
                     else Seq.cons (Seq.index t j) (union c si tj'))))
  = I.suffix_cons s i; I.suffix_cons t j

/// When `t` is used up, the rest of the union is the rest of `s`.
let union_rest_left (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires 0 <= i /\ i <= Seq.length s /\ j == Seq.length t)
          (ensures union c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t)) ==
                   Seq.slice s i (Seq.length s))
  = if i = Seq.length s then Seq.lemma_eq_elim (Seq.slice t j (Seq.length t)) (Seq.slice s i (Seq.length s))

/// When `s` is used up, the rest of the union is the rest of `t`.
let union_rest_right (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires i == Seq.length s /\ 0 <= j /\ j <= Seq.length t)
          (ensures union c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t)) ==
                   Seq.slice t j (Seq.length t))
  = ()

let union_whole (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (union c (Seq.slice s 0 (Seq.length s)) (Seq.slice t 0 (Seq.length t)) == union c s t)
  = Seq.lemma_eq_elim (Seq.slice s 0 (Seq.length s)) s;
    Seq.lemma_eq_elim (Seq.slice t 0 (Seq.length t)) t

/// The union with an empty `s` is `t`.
let union_left_empty (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (ensures Seq.length s == 0 ==> union c s t == t)
  = ()

/// Writing `x` at `k` extends the prefix `m[0..k)` by one, ahead of the rest `r` of `x :: r`.
let push_prefix (#a: Type0) (m: Seq.seq a) (k: int) (x: a) (r: Seq.seq a)
  : Lemma (requires 0 <= k /\ k < Seq.length m)
          (ensures Seq.append (Seq.slice (Seq.upd m k x) 0 (k + 1)) r ==
                   Seq.append (Seq.slice m 0 k) (Seq.cons x r))
  = I.push_prefix m k x r

/// Writing `s[i]` at `k` moves it from the rest of `s` to the prefix.
let push_rest (#a: Type0) (m: Seq.seq a) (k: int) (s: Seq.seq a) (i: int)
  : Lemma (requires 0 <= k /\ k < Seq.length m /\ 0 <= i /\ i < Seq.length s)
          (ensures Seq.append (Seq.slice (Seq.upd m k (Seq.index s i)) 0 (k + 1)) (Seq.slice s (i + 1) (Seq.length s)) ==
                   Seq.append (Seq.slice m 0 k) (Seq.slice s i (Seq.length s)))
  = I.suffix_cons s i;
    I.push_prefix m k (Seq.index s i) (Seq.slice s (i + 1) (Seq.length s))

let below (#a: Type0) (c: O.comparer a) (y: a) (u: Seq.seq a) : prop =
  forall (k: nat). k < Seq.length u ==> O.compare c y (Seq.index u k) < 0

let below_tail (#a: Type0) (c: O.comparer a) (y: a) (u: Seq.seq a)
  : Lemma (requires below c y u /\ Seq.length u > 0) (ensures below c y (Seq.tail u))
  = assert (forall (k: nat). k < Seq.length u - 1 ==> Seq.index (Seq.tail u) k == Seq.index u (k + 1))

let below_cons (#a: Type0) (c: O.comparer a) (y x: a) (u: Seq.seq a)
  : Lemma (requires O.compare c y x < 0 /\ below c y u) (ensures below c y (Seq.cons x u))
  = assert (forall (k: nat). 0 < k /\ k < Seq.length u + 1 ==> Seq.index (Seq.cons x u) k == Seq.index u (k - 1))

/// A bound below both sides is below their union.
let rec union_below (#a: Type0) (c: O.comparer a) (y: a) (s t: Seq.seq a)
  : Lemma (requires below c y s /\ below c y t)
          (ensures below c y (union c s t))
          (decreases Seq.length s + Seq.length t)
  = if Seq.length s = 0 || Seq.length t = 0 then ()
    else begin
      let o = O.compare c (Seq.head s) (Seq.head t) in
      below_tail c y s; below_tail c y t;
      if o < 0 then (union_below c y (Seq.tail s) t; below_cons c y (Seq.head s) (union c (Seq.tail s) t))
      else if o = 0 then (union_below c y (Seq.tail s) (Seq.tail t); below_cons c y (Seq.head t) (union c (Seq.tail s) (Seq.tail t)))
      else (union_below c y s (Seq.tail t); below_cons c y (Seq.head t) (union c s (Seq.tail t)))
    end

let sorted_tail (#a: Type0) (c: O.comparer a) (u: Seq.seq a)
  : Lemma (requires S.strictly_sorted c u /\ Seq.length u > 0)
          (ensures S.strictly_sorted c (Seq.tail u) /\ below c (Seq.head u) (Seq.tail u))
  = assert (forall (k: nat). k < Seq.length u - 1 ==> Seq.index (Seq.tail u) k == Seq.index u (k + 1))

let sorted_cons (#a: Type0) (c: O.comparer a) (x: a) (u: Seq.seq a)
  : Lemma (requires S.strictly_sorted c u /\ below c x u) (ensures S.strictly_sorted c (Seq.cons x u))
  = let w = Seq.cons x u in
    assert (forall (k: nat). 0 < k /\ k < Seq.length w ==> Seq.index w k == Seq.index u (k - 1));
    assert (Seq.index w 0 == x)

/// `y` below the head of a sorted `u` is below all of it.
let below_sorted (#a: Type0) (c: O.comparer a) (y: a) (u: Seq.seq a)
  : Lemma (requires S.strictly_sorted c u /\ Seq.length u > 0 /\ O.compare c y (Seq.head u) <= 0)
          (ensures below c y (Seq.tail u))
  = let l (k: nat{k < Seq.length (Seq.tail u)}) : Lemma (O.compare c y (Seq.index (Seq.tail u) k) < 0) =
      assert (Seq.index (Seq.tail u) k == Seq.index u (k + 1));
      O.compare_trans c y (Seq.head u) (Seq.index u (k + 1))
    in
    FStar.Classical.forall_intro l

let below_sorted_all (#a: Type0) (c: O.comparer a) (y: a) (u: Seq.seq a)
  : Lemma (requires S.strictly_sorted c u /\ Seq.length u > 0 /\ O.compare c y (Seq.head u) < 0)
          (ensures below c y u)
  = let l (k: nat{k < Seq.length u}) : Lemma (O.compare c y (Seq.index u k) < 0) =
      if k > 0 then O.compare_trans c y (Seq.head u) (Seq.index u k)
    in
    FStar.Classical.forall_intro l

/// The union of two strictly sorted sequences is strictly sorted, and no longer than both.
let rec union_sorted (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t)
          (ensures S.strictly_sorted c (union c s t) /\
                   Seq.length (union c s t) <= Seq.length s + Seq.length t)
          (decreases Seq.length s + Seq.length t)
  = if Seq.length s = 0 || Seq.length t = 0 then ()
    else begin
      let x = Seq.head s in
      let y = Seq.head t in
      let o = O.compare c x y in
      sorted_tail c s; sorted_tail c t;
      if o < 0 then begin
        union_sorted c (Seq.tail s) t;
        below_sorted_all c x t;
        union_below c x (Seq.tail s) t;
        sorted_cons c x (union c (Seq.tail s) t)
      end else if o = 0 then begin
        union_sorted c (Seq.tail s) (Seq.tail t);
        below_sorted c y s;
        union_below c y (Seq.tail s) (Seq.tail t);
        sorted_cons c y (union c (Seq.tail s) (Seq.tail t))
      end else begin
        union_sorted c s (Seq.tail t);
        below_sorted_all c y s;
        union_below c y s (Seq.tail t);
        sorted_cons c y (union c s (Seq.tail t))
      end
    end

/// One step of `AddAllElements`: insert `x` unless a member compares equal to it.
let add_one (#a: Type0) (c: O.comparer a) (u: Seq.seq a) (x: a) : Seq.seq a =
  if S.key_index c u x >= 0 then u else TH.inserted c u x

/// `s` after adding each element of `t`, first to last.
let rec add_all (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Tot (Seq.seq a) (decreases Seq.length t) =
  if Seq.length t = 0 then s
  else add_one c (add_all c s (Seq.slice t 0 (Seq.length t - 1))) (Seq.index t (Seq.length t - 1))

let add_all_step (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: int)
  : Lemma (requires 0 <= i /\ i < Seq.length t)
          (ensures add_all c s (Seq.slice t 0 (i + 1)) ==
                   add_one c (add_all c s (Seq.slice t 0 i)) (Seq.index t i))
  = Seq.lemma_eq_elim (Seq.slice (Seq.slice t 0 (i + 1)) 0 i) (Seq.slice t 0 i)

let add_all_whole (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (add_all c s (Seq.slice t 0 (Seq.length t)) == add_all c s t)
  = Seq.lemma_eq_elim (Seq.slice t 0 (Seq.length t)) t

let add_one_length (#a: Type0) (c: O.comparer a) (u: Seq.seq a) (x: a)
  : Lemma (Seq.length (add_one c u x) <= Seq.length u + 1)
  = if S.key_index c u x >= 0 then () else TH.inserted_length c u x

let rec add_all_length_ (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (ensures Seq.length (add_all c s t) <= Seq.length s + Seq.length t)
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else begin
      let t' = Seq.slice t 0 (Seq.length t - 1) in
      add_all_length_ c s t';
      add_one_length c (add_all c s t') (Seq.index t (Seq.length t - 1))
    end

/// The length of `s` after adding the first `i` elements of `t`.
let add_all_length (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: int)
  : Lemma (ensures 0 <= i /\ i <= Seq.length t ==>
                   Seq.length (add_all c s (Seq.slice t 0 i)) <= Seq.length s + i)
  = if 0 <= i && i <= Seq.length t then add_all_length_ c s (Seq.slice t 0 i)

/// When one side is used up, the rest of the merge is the rest of the other.
let union_rest (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires 0 <= i /\ i <= Seq.length s /\ 0 <= j /\ j <= Seq.length t)
          (ensures (i == Seq.length s ==> union c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t)) ==
                                         Seq.slice t j (Seq.length t)) /\
                   (j == Seq.length t ==> union c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t)) ==
                                         Seq.slice s i (Seq.length s)))
  = if i = Seq.length s then union_rest_right c s t i j;
    if j = Seq.length t then union_rest_left c s t i j

/// A prefix followed by nothing of `s` is the prefix.
let rest_done (#a: Type0) (p s: Seq.seq a)
  : Lemma (Seq.append p (Seq.slice s (Seq.length s) (Seq.length s)) == p)
  = Seq.lemma_eq_elim (Seq.append p (Seq.slice s (Seq.length s) (Seq.length s))) p

/// Flipping, in order, the elements of a strictly sorted `t` into the empty set inserts
/// each at the end, giving `t`: `SymmetricExceptWith` on an empty set is `UnionWith`.
let rec sym_except_empty (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires Seq.length s == 0 /\ S.strictly_sorted c t)
          (ensures Pulse.Lib.CSharp.SetOps.sym_except c s t == t)
          (decreases Seq.length t)
  = if Seq.length t = 0 then Seq.lemma_eq_elim s t
    else begin
      let n = Seq.length t - 1 in
      let t' = Seq.slice t 0 n in
      let x = Seq.index t n in
      sym_except_empty c s t';
      Pulse.Lib.CSharp.SearchTree.lower_bound_all_below c t' x;
      Pulse.Lib.CSharp.TopDown.seq_ins_index t' n x 0;
      Seq.lemma_eq_elim (TH.inserted c t' x) t
    end

let sym_except_union_empty (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires Seq.length s == 0 /\ S.strictly_sorted c t)
          (ensures Pulse.Lib.CSharp.SetOps.sym_except c s t == union c s t)
  = sym_except_empty c s t; union_left_empty c s t
