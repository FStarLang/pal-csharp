module SortedSetInductive.RangeCounts

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module C = SortedSetCount
module I = SortedSetInductive.IteratorSpec

#set-options "--z3rlimit 10"

let inside_ok (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (x: a)
  : Lemma (requires I.bounds lo hi la ua)
      (ensures I.inside c lo hi la ua x <==> C.ok_s c lo hi la ua x) =
  C.ok_s_def c lo hi la ua

let ok_equiv (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (x y: a)
  : Lemma (requires O.compare c x y == 0)
      (ensures C.ok_s c lo hi la ua x == C.ok_s c lo hi la ua y) =
  C.ok_s_def c lo hi la ua;
  if C.has_bound lo hi la ua then
    C.in_range_equiv c (C.pk lo hi) (C.pk hi lo) la ua x y

let filter_snoc (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (s: Seq.seq a) (x: a)
  : Lemma (requires I.bounds lo hi la ua)
      (ensures I.filter c lo hi la ua (Seq.snoc s x) ==
        (if C.ok_s c lo hi la ua x then Seq.snoc (I.filter c lo hi la ua s) x
         else I.filter c lo hi la ua s)) =
  Seq.lemma_eq_intro (Seq.snoc s x) (Seq.append s (Seq.cons x Seq.empty));
  I.filter_append c lo hi la ua s (Seq.cons x Seq.empty);
  I.filter_cons c lo hi la ua x Seq.empty;
  inside_ok c lo hi la ua x;
  if C.ok_s c lo hi la ua x then
    Seq.lemma_eq_intro (Seq.append (I.filter c lo hi la ua s) (Seq.cons x Seq.empty))
      (Seq.snoc (I.filter c lo hi la ua s) x)
  else Seq.lemma_eq_intro (Seq.append (I.filter c lo hi la ua s) Seq.empty)
      (I.filter c lo hi la ua s)

let rec found_prefix (#a: Type0) (c: O.comparer a) (ok: a -> bool)
    (ks kt s: Seq.seq a) (n: nat{n <= Seq.length ks /\ n <= Seq.length kt})
  : Lemma (requires forall (j: nat). j < n ==> Seq.index ks j == Seq.index kt j)
      (ensures C.found_upto c ok ks s n == C.found_upto c ok kt s n)
      (decreases n) =
  if n > 0 then found_prefix c ok ks kt s (n - 1)

let found_key_snoc (#a: Type0) (c: O.comparer a) (ok: a -> bool)
    (ks s: Seq.seq a) (x: a)
  : Lemma (C.found c ok (Seq.snoc ks x) s ==
      C.found c ok ks s + (if ok x && C.hit c s x then 1 else 0)) =
  found_prefix c ok (Seq.snoc ks x) ks s (Seq.length ks)

let rec found_filter (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (ks s: Seq.seq a)
  : Lemma (requires I.bounds lo hi la ua)
      (ensures C.found_s c lo hi la ua ks s == C.found_all c (I.filter c lo hi la ua ks) s)
      (decreases Seq.length ks) =
  if Seq.length ks = 0 then ()
  else (
    let rest = C.init ks in
    let x = Seq.last ks in
    Seq.lemma_eq_intro (Seq.snoc rest x) ks;
    found_filter c lo hi la ua rest s;
    filter_snoc c lo hi la ua rest x;
    found_key_snoc c (C.ok_s c lo hi la ua) rest s x;
    if C.ok_s c lo hi la ua x then
      found_key_snoc c C.all_ok (I.filter c lo hi la ua rest) s x)

let rec hit_filter (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (ks: Seq.seq a) (y: a)
  : Lemma (requires I.bounds lo hi la ua)
      (ensures C.hit c (I.filter c lo hi la ua ks) y ==
        (C.ok_s c lo hi la ua y && C.hit c ks y))
      (decreases Seq.length ks) =
  if Seq.length ks = 0 then ()
  else (
    let rest = C.init ks in
    let x = Seq.last ks in
    Seq.lemma_eq_intro (Seq.snoc rest x) ks;
    hit_filter c lo hi la ua rest y;
    filter_snoc c lo hi la ua rest x;
    C.hit_snoc c rest x y;
    if O.compare c x y = 0 then ok_equiv c lo hi la ua x y;
    if C.ok_s c lo hi la ua x then
      C.hit_snoc c (I.filter c lo hi la ua rest) x y)

let rec unfound_filter (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (ks s: Seq.seq a)
  : Lemma (requires I.bounds lo hi la ua /\ S.strictly_sorted c ks)
      (ensures C.unfound_s c lo hi la ua ks s == C.unfound_all c (I.filter c lo hi la ua ks) s)
      (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else (
    unfound_filter c lo hi la ua ks (C.init s);
    I.filter_sorted c lo hi la ua ks;
    C.sorted_hit c ks (Seq.last s);
    C.sorted_hit c (I.filter c lo hi la ua ks) (Seq.last s);
    hit_filter c lo hi la ua ks (Seq.last s))

let counts (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (ks s: Seq.seq a)
  : Lemma (requires I.bounds lo hi la ua /\ S.strictly_sorted c ks)
      (ensures C.found_s c lo hi la ua ks s == C.found_all c (I.filter c lo hi la ua ks) s /\
        C.unfound_s c lo hi la ua ks s == C.unfound_all c (I.filter c lo hi la ua ks) s) =
  found_filter c lo hi la ua ks s;
  unfound_filter c lo hi la ua ks s
