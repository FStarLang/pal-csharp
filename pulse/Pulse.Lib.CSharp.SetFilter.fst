module Pulse.Lib.CSharp.SetFilter

/// R27.40. Membership in a sequence, and what it takes to remove a set of members from a
/// strictly sorted sequence one at a time: `SortedSet<T>.RemoveWhere`, which collects the
/// matching items in a breadth-first walk and then removes them.
///
/// * `contains s y`: `y` is an element of `s` (F*'s equality; no comparer).
/// * `removing c s0 s m i`: the items `m[i+1..]` have been removed from `s0`, leaving `s`.
/// * `filter_unique`: a strictly sorted sequence is determined by its members, so the set
///   left is `Pal.RemoveAll` of the one before.
///
/// Everything is proved from `Pulse.Lib.CSharp.Order`'s axioms; nothing new is trusted.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module D = Pulse.Lib.CSharp.Delegate
module F = Pulse.Lib.CSharp.Find
module TR = Pulse.Lib.CSharp.TopDownRemove

/// `y` is one of `s[lo..]`.
let contains_from (#a: Type0) (s: Seq.seq a) (lo: int) (y: a) : prop =
  exists (j: nat). lo <= j /\ j < Seq.length s /\ Seq.index s j == y

let contains (#a: Type0) (s: Seq.seq a) (y: a) : prop = contains_from s 0 y

/// Where a member is.
let witness (#a: Type0) (s: Seq.seq a) (y: a)
  : Ghost nat (requires contains s y) (ensures fun j -> j < Seq.length s /\ Seq.index s j == y)
  = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun j -> j < Seq.length s /\ Seq.index s j == y)

let contains_index (#a: Type0) (s: Seq.seq a) (j: nat)
  : Lemma (requires j < Seq.length s) (ensures contains s (Seq.index s j))
          [SMTPat (contains s (Seq.index s j))]
  = ()

let contains_empty (#a: Type0) (y: a)
  : Lemma (~(contains (Seq.empty #a) y)) [SMTPat (contains (Seq.empty #a) y)]
  = ()

let contains_append (#a: Type0) (s1 s2: Seq.seq a) (y: a)
  : Lemma (contains (Seq.append s1 s2) y <==> contains s1 y \/ contains s2 y)
          [SMTPat (contains (Seq.append s1 s2) y)]
  = let s = Seq.append s1 s2 in
    let fwd (j: nat) : Lemma (requires j < Seq.length s /\ Seq.index s j == y)
                             (ensures contains s1 y \/ contains s2 y)
      = if j < Seq.length s1 then () else assert (Seq.index s2 (j - Seq.length s1) == y) in
    let bwd1 (j: nat) : Lemma (requires j < Seq.length s1 /\ Seq.index s1 j == y) (ensures contains s y)
      = assert (Seq.index s j == y) in
    let bwd2 (j: nat) : Lemma (requires j < Seq.length s2 /\ Seq.index s2 j == y) (ensures contains s y)
      = assert (Seq.index s (Seq.length s1 + j) == y) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fwd);
    FStar.Classical.forall_intro (FStar.Classical.move_requires bwd1);
    FStar.Classical.forall_intro (FStar.Classical.move_requires bwd2)

let contains_cons (#a: Type0) (k: a) (s: Seq.seq a) (y: a)
  : Lemma (contains (Seq.cons k s) y <==> k == y \/ contains s y)
          [SMTPat (contains (Seq.cons k s) y)]
  = contains_append (Seq.create 1 k) s y

let contains_snoc (#a: Type0) (s: Seq.seq a) (k: a) (y: a)
  : Lemma (contains (Seq.snoc s k) y <==> contains s y \/ k == y)
          [SMTPat (contains (Seq.snoc s k) y)]
  = contains_append s (Seq.create 1 k) y

let contains_from_step (#a: Type0) (s: Seq.seq a) (i: nat) (y: a)
  : Lemma (requires i < Seq.length s)
          (ensures contains_from s i y <==> Seq.index s i == y \/ contains_from s (i + 1) y)
  = ()

(* ------------------------------------------------------------------------------------ *)
(* Strictly sorted sequences                                                            *)

/// Two members of a strictly sorted sequence that compare equal are the same.
let sorted_cmp_eq (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (y k: a)
  : Lemma (requires S.strictly_sorted c s /\ contains s y /\ contains s k /\ O.compare c y k == 0)
          (ensures y == k)
  = let p = witness s y in
    let q = witness s k in
    if p < q then assert (O.compare c (Seq.index s p) (Seq.index s q) < 0)
    else if q < p then assert (O.compare c (Seq.index s q) (Seq.index s p) < 0)
    else ()

/// The members of a strictly sorted `s` with its element at `p` deleted.
let seq_del_facts (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (p: nat)
  : Lemma (requires S.strictly_sorted c s /\ p < Seq.length s)
          (ensures (let s' = TR.seq_del s p in
                    Seq.length s' == Seq.length s - 1 /\ S.strictly_sorted c s' /\
                    (forall (y: a). contains s' y <==> contains s y /\ ~(y == Seq.index s p))))
  = let s' = TR.seq_del s p in
    let k = Seq.index s p in
    let fwd (y: a) : Lemma (requires contains s' y) (ensures contains s y /\ ~(y == k))
      = let j = witness s' y in
        let j' = if j < p then j else j + 1 in
        assert (Seq.index s j' == y);
        if j' < p then assert (O.compare c (Seq.index s j') (Seq.index s p) < 0)
        else assert (O.compare c (Seq.index s p) (Seq.index s j') < 0) in
    let bwd (y: a) : Lemma (requires contains s y /\ ~(y == k)) (ensures contains s' y)
      = let j = witness s y in
        if j < p then assert (Seq.index s' j == y)
        else assert (Seq.index s' (j - 1) == y) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fwd);
    FStar.Classical.forall_intro (FStar.Classical.move_requires bwd)

/// `key_index` of a member of a strictly sorted sequence is where it is.
let key_index_member (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (p: nat)
  : Lemma (requires S.strictly_sorted c s /\ p < Seq.length s)
          (ensures S.key_index c s (Seq.index s p) == p /\
                   TR.removed c s (Seq.index s p) == TR.seq_del s p)
  = let sa = Seq.slice s 0 p in
    let x = Seq.index s p in
    let sb = Seq.slice s (p + 1) (Seq.length s) in
    Seq.lemma_eq_intro s (Seq.append sa (Seq.cons x sb));
    TR.key_index_pivot c sa x sb x;
    TR.seq_del_pivot sa x sb

(* ------------------------------------------------------------------------------------ *)
(* Removing collected members one at a time                                             *)

/// `m[i+1..]` have been removed from the strictly sorted `s0`, leaving the strictly
/// sorted `s`; every one of `m` is a member of `s0`.
let removing (#a: Type0) (c: O.comparer a) (s0 s m: Seq.seq a) (i: int) : prop =
  -1 <= i /\ i < Seq.length m /\
  S.strictly_sorted c s0 /\ S.strictly_sorted c s /\
  (forall (j: nat). j < Seq.length m ==> contains s0 (Seq.index m j)) /\
  (forall (y: a). {:pattern contains s y} contains s y <==> contains s0 y /\ ~(contains_from m (i + 1) y))

let removing_start (#a: Type0) (c: O.comparer a) (s0 m: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s0 /\ (forall (y: a). contains m y ==> contains s0 y))
          (ensures removing c s0 s0 m (Seq.length m - 1))
  = ()

/// Removing `m[i]`: it is there exactly when the set has an element equivalent to it, and
/// what is left has `m[i..]` removed.
let removing_step (#a: Type0) (c: O.comparer a) (s0 s m: Seq.seq a) (i: int)
  : Lemma (requires removing c s0 s m i /\ 0 <= i)
          (ensures (let k = Seq.index m i in
                    let s' = TR.removed c s k in
                    (S.key_index c s k >= 0 <==> contains s k) /\
                    Seq.length s' == Seq.length s - (if S.key_index c s k >= 0 then 1 else 0) /\
                    removing c s0 s' m (i - 1)))
  = let k = Seq.index m i in
    let s' = TR.removed c s k in
    FStar.Classical.forall_intro (contains_from_step m i);
    let lb = S.key_index c s k in
    if lb >= 0 then begin
      let y = Seq.index s lb in
      assert (contains s y);
      sorted_cmp_eq c s0 y k;
      key_index_member c s lb;
      seq_del_facts c s lb
    end else begin
      let not_in () : Lemma (requires contains s k) (ensures False)
        = let p = witness s k in
          key_index_member c s p in
      FStar.Classical.move_requires not_in ()
    end

(* ------------------------------------------------------------------------------------ *)
(* A strictly sorted sequence is its members                                            *)

let rec filter_prefix_facts (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (f: D.fn1 a bool) (keep: bool)
    (n: nat { n <= Seq.length s })
  : Lemma (requires S.strictly_sorted c s)
          (ensures S.strictly_sorted c (F.filter_prefix s f keep n) /\
                   (forall (y: a). contains (F.filter_prefix s f keep n) y <==>
                                   (exists (j: nat). j < n /\ Seq.index s j == y) /\ D.apply1 f y == keep))
          (decreases n)
  = if n = 0 then ()
    else begin
      filter_prefix_facts c s f keep (n - 1);
      let r = F.filter_prefix s f keep (n - 1) in
      let x = Seq.index s (n - 1) in
      if D.apply1 f x = keep then begin
        let r' = Seq.snoc r x in
        let lt (j: nat { j < Seq.length r }) : Lemma (O.compare c (Seq.index r j) x < 0)
          = assert (contains r (Seq.index r j)) in
        FStar.Classical.forall_intro lt;
        let srt (i: nat) (j: nat { i < j /\ j < Seq.length r' })
          : Lemma (O.compare c (Seq.index r' i) (Seq.index r' j) < 0)
          = if j < Seq.length r then () else lt i in
        introduce forall (i j: nat). i < j /\ j < Seq.length r' ==>
                                     O.compare c (Seq.index r' i) (Seq.index r' j) < 0
        with introduce _ ==> _ with srt i j
      end
    end

let filter_facts (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (f: D.fn1 a bool) (keep: bool)
  : Lemma (requires S.strictly_sorted c s)
          (ensures S.strictly_sorted c (F.filter s f keep) /\
                   (forall (y: a). contains (F.filter s f keep) y <==> contains s y /\ D.apply1 f y == keep))
  = filter_prefix_facts c s f keep (Seq.length s)

let rec sorted_unique (#a: Type0) (c: O.comparer a) (s1 s2: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s1 /\ S.strictly_sorted c s2 /\
                    (forall (y: a). contains s1 y <==> contains s2 y))
          (ensures s1 == s2)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then begin
      if Seq.length s2 > 0 then assert (contains s2 (Seq.index s2 0));
      Seq.lemma_eq_intro s1 s2
    end
    else begin
      let h1 = Seq.index s1 0 in
      assert (contains s1 h1);
      assert (Seq.length s2 > 0);
      let h2 = Seq.index s2 0 in
      assert (contains s2 h2);
      let le (s: Seq.seq a) (y: a) : Lemma (requires S.strictly_sorted c s /\ contains s y /\ Seq.length s > 0)
                                           (ensures O.compare c (Seq.index s 0) y <= 0)
        = let p = witness s y in
          if p = 0 then () else () in
      le s1 h2; le s2 h1;
      sorted_cmp_eq c s1 h1 h2;
      let t1 = Seq.tail s1 in
      let t2 = Seq.tail s2 in
      Seq.lemma_eq_intro s1 (Seq.cons h1 t1);
      Seq.lemma_eq_intro s2 (Seq.cons h2 t2);
      let notin (s t: Seq.seq a) (y: a)
        : Lemma (requires S.strictly_sorted c s /\ Seq.length s > 0 /\ t == Seq.tail s)
                (ensures S.strictly_sorted c t /\ (contains t y <==> contains s y /\ ~(y == Seq.index s 0)))
        = Seq.lemma_eq_intro t (TR.seq_del s 0); seq_del_facts c s 0 in
      FStar.Classical.forall_intro (FStar.Classical.move_requires (notin s1 t1));
      FStar.Classical.forall_intro (FStar.Classical.move_requires (notin s2 t2));
      sorted_unique c t1 t2
    end

/// R27.40. What `RemoveWhere` leaves: a strictly sorted `s` whose members are those of `s0`
/// that `f` does not hold of is `Pal.RemoveAll(s0, f)`.
let filter_unique (#a: Type0) (c: O.comparer a) (s0 s: Seq.seq a) (f: D.fn1 a bool)
  : Lemma (requires S.strictly_sorted c s0 /\ S.strictly_sorted c s /\
                    (forall (y: a). contains s y <==> contains s0 y /\ D.apply1 f y == false))
          (ensures s == F.filter s0 f false)
  = filter_facts c s0 f false;
    sorted_unique c s (F.filter s0 f false)
