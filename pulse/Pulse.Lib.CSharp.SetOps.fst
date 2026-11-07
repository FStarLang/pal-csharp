module Pulse.Lib.CSharp.SetOps

/// R27.51. Set operations of `SortedSet<T>` over another set of the same comparer, which
/// it computes by enumerating the other set.
///
/// * `overlaps c s t`: some element of `t` is a member of the strictly sorted `s` under
///   `c` (`key_index c s x >= 0`), as `Overlaps` decides it; with `overlaps_step` and
///   `overlaps_whole`, the steps of a walk over the suffixes of `t`.
/// * `overlaps_empty` (a pattern), `overlaps_disjoint`: the shortcuts `Overlaps` takes,
///   when `s` is empty and when the two strictly sorted sequences lie in disjoint ranges.
///
/// Everything is proved from `Pulse.Lib.CSharp.Order`'s axioms; nothing new is trusted.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted

let rec overlaps (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Tot bool (decreases Seq.length t) =
  if Seq.length t = 0 then false
  else S.key_index c s (Seq.index t 0) >= 0 || overlaps c s (Seq.tail t)

let overlaps_step (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: int)
  : Lemma (requires 0 <= i /\ i <= Seq.length t)
          (ensures overlaps c s (Seq.slice t i (Seq.length t)) ==
                   (if i = Seq.length t then false
                    else S.key_index c s (Seq.index t i) >= 0 ||
                         overlaps c s (Seq.slice t (i + 1) (Seq.length t))))
  = if i = Seq.length t then ()
    else Seq.lemma_eq_elim (Seq.tail (Seq.slice t i (Seq.length t))) (Seq.slice t (i + 1) (Seq.length t))

let overlaps_whole (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (overlaps c s (Seq.slice t 0 (Seq.length t)) == overlaps c s t)
  = Seq.lemma_eq_elim (Seq.slice t 0 (Seq.length t)) t

/// `overlaps` is: some position of `t` holds a member of `s`.
let rec overlaps_at (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (ensures overlaps c s t <==>
                   (exists (i: nat). i < Seq.length t /\ S.key_index c s (Seq.index t i) >= 0))
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else begin
      overlaps_at c s (Seq.tail t);
      assert (forall (i: nat). 0 < i /\ i < Seq.length t ==> Seq.index (Seq.tail t) (i - 1) == Seq.index t i)
    end

let overlaps_empty (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires Seq.length s == 0) (ensures overlaps c s t == false)
          [SMTPat (overlaps c s t)]
  = overlaps_at c s t

/// A member of a strictly sorted `s` lies between its first and last elements.
let key_index_bounds (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x: a)
  : Lemma (requires S.strictly_sorted c s /\ S.key_index c s x >= 0)
          (ensures O.compare c (Seq.index s 0) x <= 0 /\
                   O.compare c x (Seq.index s (Seq.length s - 1)) <= 0)
  = let k = S.key_index c s x in
    let sk = Seq.index s k in
    assert (O.compare c sk x == 0);
    if k > 0 then O.compare_trans c (Seq.index s 0) sk x;
    if k < Seq.length s - 1 then O.compare_trans c x sk (Seq.index s (Seq.length s - 1))

/// Two strictly sorted sequences whose ranges are disjoint share no member.
let overlaps_disjoint (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t /\
                    Seq.length s > 0 /\ Seq.length t > 0 /\
                    (O.compare c (Seq.index s 0) (Seq.index t (Seq.length t - 1)) > 0 \/
                     O.compare c (Seq.index s (Seq.length s - 1)) (Seq.index t 0) < 0))
          (ensures overlaps c s t == false)
  = overlaps_at c s t;
    let none (i: nat) : Lemma (i < Seq.length t ==> S.key_index c s (Seq.index t i) < 0) =
      if i < Seq.length t && S.key_index c s (Seq.index t i) >= 0 then begin
        let x = Seq.index t i in
        key_index_bounds c s x;
        let t0 = Seq.index t 0 in
        let tn = Seq.index t (Seq.length t - 1) in
        if i > 0 then assert (O.compare c t0 x < 0);
        if i < Seq.length t - 1 then assert (O.compare c x tn < 0);
        O.compare_trans c (Seq.index s 0) x tn;
        O.compare_trans c t0 x (Seq.index s (Seq.length s - 1))
      end
    in
    FStar.Classical.forall_intro none
