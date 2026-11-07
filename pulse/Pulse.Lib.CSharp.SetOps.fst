module Pulse.Lib.CSharp.SetOps

/// R27.51. Set operations of `SortedSet<T>` over another set of the same comparer, which
/// it computes by enumerating the other set.
///
/// * `overlaps c s t`: some element of `t` is a member of the strictly sorted `s` under
///   `c` (`key_index c s x >= 0`), as `Overlaps` decides it; with `overlaps_step` and
///   `overlaps_whole`, the steps of a walk over the suffixes of `t`.
/// * `overlaps_empty` (a pattern), `overlaps_disjoint`: the shortcuts `Overlaps` takes,
///   when `s` is empty and when the two strictly sorted sequences lie in disjoint ranges.
/// * `except c s t`: `s` after removing (`TopDownRemove.removed`) each element of `t` in
///   turn, as `ExceptWith` computes it. With `except_step`, `except_skip`,
///   `except_break`, `except_disjoint` and `except_empty`, the steps and shortcuts of
///   `ExceptWith`.
/// * `sym_except c s t`: `s` after, for each element of `t` in turn, removing it if it is
///   a member and inserting it (`TopDownHeap.inserted`) if not, as
///   `SymmetricExceptWith` computes it; `sym_except_length` bounds its length by
///   `|s| + |t|`, which is what keeps `Add`'s count from overflowing.
///
/// Everything is proved from `Pulse.Lib.CSharp.Order`'s axioms; nothing new is trusted.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module TR = Pulse.Lib.CSharp.TopDownRemove
module TH = Pulse.Lib.CSharp.TopDownHeap

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


/// `s` after removing each element of `t`, first to last.
let rec except (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Tot (Seq.seq a) (decreases Seq.length t) =
  if Seq.length t = 0 then s
  else TR.removed c (except c s (Seq.slice t 0 (Seq.length t - 1))) (Seq.index t (Seq.length t - 1))

let except_step (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: int)
  : Lemma (requires 0 <= i /\ i < Seq.length t)
          (ensures except c s (Seq.slice t 0 (i + 1)) ==
                   TR.removed c (except c s (Seq.slice t 0 i)) (Seq.index t i))
  = Seq.lemma_eq_elim (Seq.slice (Seq.slice t 0 (i + 1)) 0 i) (Seq.slice t 0 i)

let except_whole (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (except c s (Seq.slice t 0 (Seq.length t)) == except c s t)
  = Seq.lemma_eq_elim (Seq.slice t 0 (Seq.length t)) t

/// Removing anything from an empty sequence leaves it empty.
let rec except_empty (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires Seq.length s == 0) (ensures except c s t == s)
          (decreases Seq.length t)
          [SMTPat (except c s t)]
  = if Seq.length t = 0 then ()
    else except_empty c s (Seq.slice t 0 (Seq.length t - 1))

/// Every element of `u` lies in `[lo, hi]`.
let within (#a: Type0) (c: O.comparer a) (lo hi: a) (u: Seq.seq a) : prop =
  forall (k: nat). k < Seq.length u ==>
    O.compare c lo (Seq.index u k) <= 0 /\ O.compare c (Seq.index u k) hi <= 0

let removed_within (#a: Type0) (c: O.comparer a) (lo hi: a) (u: Seq.seq a) (x: a)
  : Lemma (requires within c lo hi u) (ensures within c lo hi (TR.removed c u x))
  = let i = S.key_index c u x in
    if i >= 0 then begin
      let r = TR.removed c u x in
      assert (forall (k: nat). k < Seq.length r ==>
                Seq.index r k == Seq.index u (if k < i then k else k + 1))
    end

let rec except_within (#a: Type0) (c: O.comparer a) (lo hi: a) (s t: Seq.seq a)
  : Lemma (requires within c lo hi s) (ensures within c lo hi (except c s t))
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else begin
      except_within c lo hi s (Seq.slice t 0 (Seq.length t - 1));
      removed_within c lo hi (except c s (Seq.slice t 0 (Seq.length t - 1))) (Seq.index t (Seq.length t - 1))
    end

/// Removing a key outside `[lo, hi]` from a sequence within it changes nothing.
let removed_outside (#a: Type0) (c: O.comparer a) (lo hi: a) (u: Seq.seq a) (x: a)
  : Lemma (requires within c lo hi u /\ (O.compare c x lo < 0 \/ O.compare c x hi > 0))
          (ensures TR.removed c u x == u)
  = let i = S.key_index c u x in
    if i >= 0 then begin
      let y = Seq.index u i in
      assert (O.compare c y x == 0);
      if O.compare c x lo < 0 then O.compare_trans c lo y x
      else O.compare_trans c x y hi
    end

let strictly_sorted_within (#a: Type0) (c: O.comparer a) (s: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ Seq.length s > 0)
          (ensures within c (Seq.index s 0) (Seq.index s (Seq.length s - 1)) s)
  = ()

let except_skip_ (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: nat{i < Seq.length t})
  : Lemma (requires S.strictly_sorted c s /\ Seq.length s > 0 /\
                    (O.compare c (Seq.index t i) (Seq.index s 0) < 0 \/
                     O.compare c (Seq.index t i) (Seq.index s (Seq.length s - 1)) > 0))
          (ensures except c s (Seq.slice t 0 (i + 1)) == except c s (Seq.slice t 0 i))
  = let lo = Seq.index s 0 in
    let hi = Seq.index s (Seq.length s - 1) in
    strictly_sorted_within c s;
    except_within c lo hi s (Seq.slice t 0 i);
    except_step c s t i;
    removed_outside c lo hi (except c s (Seq.slice t 0 i)) (Seq.index t i)

/// `ExceptWith`'s `continue` and `break`: an element of `t` outside the range of `s`
/// removes nothing.
let except_skip (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: int)
  : Lemma (ensures S.strictly_sorted c s /\ Seq.length s > 0 /\ 0 <= i /\ i < Seq.length t /\
                   (O.compare c (Seq.index t i) (Seq.index s 0) < 0 \/
                    O.compare c (Seq.index t i) (Seq.index s (Seq.length s - 1)) > 0) ==>
                   except c s (Seq.slice t 0 (i + 1)) == except c s (Seq.slice t 0 i))
  = if 0 <= i && i < Seq.length t then FStar.Classical.move_requires (except_skip_ c s t) i

let rec except_above (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: nat)
  : Lemma (requires S.strictly_sorted c s /\ Seq.length s > 0 /\ S.strictly_sorted c t /\
                    i < Seq.length t /\ i <= j /\ j <= Seq.length t /\
                    O.compare c (Seq.index t i) (Seq.index s (Seq.length s - 1)) > 0)
          (ensures except c s (Seq.slice t 0 j) == except c s (Seq.slice t 0 i))
          (decreases j)
  = if j = i then ()
    else begin
      except_above c s t i (j - 1);
      if j - 1 > i then
        O.compare_trans c (Seq.index s (Seq.length s - 1)) (Seq.index t i) (Seq.index t (j - 1));
      except_skip_ c s t (j - 1)
    end

let except_break_ (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: nat{i < Seq.length t})
  : Lemma (requires S.strictly_sorted c s /\ Seq.length s > 0 /\ S.strictly_sorted c t /\
                    O.compare c (Seq.index t i) (Seq.index s (Seq.length s - 1)) > 0)
          (ensures except c s t == except c s (Seq.slice t 0 i))
  = except_above c s t i (Seq.length t);
    except_whole c s t

/// `ExceptWith`'s `break`: past the range of `s`, the rest of a strictly sorted `t`
/// removes nothing.
let except_break (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: int)
  : Lemma (ensures S.strictly_sorted c s /\ Seq.length s > 0 /\ S.strictly_sorted c t /\
                   0 <= i /\ i < Seq.length t /\
                   O.compare c (Seq.index t i) (Seq.index s (Seq.length s - 1)) > 0 ==>
                   except c s t == except c s (Seq.slice t 0 i))
  = if 0 <= i && i < Seq.length t then FStar.Classical.move_requires (except_break_ c s t) i

let rec except_none (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires forall (k: nat). k < Seq.length t ==> S.key_index c s (Seq.index t k) < 0)
          (ensures except c s t == s)
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else except_none c s (Seq.slice t 0 (Seq.length t - 1))

/// `ExceptWith`'s range test: when the ranges of `s` and `t` are disjoint, nothing is
/// removed.
let except_disjoint (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t /\ Seq.length s > 0 /\
                    (Seq.length t > 0 ==>
                       O.compare c (Seq.index t (Seq.length t - 1)) (Seq.index s 0) < 0 \/
                       O.compare c (Seq.index t 0) (Seq.index s (Seq.length s - 1)) > 0))
          (ensures except c s t == s)
  = if Seq.length t = 0 then ()
    else begin
      overlaps_disjoint c s t;
      overlaps_at c s t;
      except_none c s t
    end


/// One step of `SymmetricExceptWith`: remove a member, insert a non-member.
let sym_flip (#a: Type0) (c: O.comparer a) (u: Seq.seq a) (x: a) : Seq.seq a =
  if S.key_index c u x >= 0 then TR.removed c u x else TH.inserted c u x

/// `s` after flipping the membership of each element of `t`, first to last.
let rec sym_except (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Tot (Seq.seq a) (decreases Seq.length t) =
  if Seq.length t = 0 then s
  else sym_flip c (sym_except c s (Seq.slice t 0 (Seq.length t - 1))) (Seq.index t (Seq.length t - 1))

let sym_except_step (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: int)
  : Lemma (requires 0 <= i /\ i < Seq.length t)
          (ensures sym_except c s (Seq.slice t 0 (i + 1)) ==
                   sym_flip c (sym_except c s (Seq.slice t 0 i)) (Seq.index t i))
  = Seq.lemma_eq_elim (Seq.slice (Seq.slice t 0 (i + 1)) 0 i) (Seq.slice t 0 i)

let sym_except_whole (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (sym_except c s (Seq.slice t 0 (Seq.length t)) == sym_except c s t)
  = Seq.lemma_eq_elim (Seq.slice t 0 (Seq.length t)) t

let sym_flip_length (#a: Type0) (c: O.comparer a) (u: Seq.seq a) (x: a)
  : Lemma (Seq.length (sym_flip c u x) <= Seq.length u + 1)
  = if S.key_index c u x >= 0 then () else TH.inserted_length c u x

let rec sym_except_length_ (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (ensures Seq.length (sym_except c s t) <= Seq.length s + Seq.length t)
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else begin
      let t' = Seq.slice t 0 (Seq.length t - 1) in
      sym_except_length_ c s t';
      sym_flip_length c (sym_except c s t') (Seq.index t (Seq.length t - 1))
    end

/// The length of `s` after flipping the first `i` elements of `t`.
let sym_except_length (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i: int)
  : Lemma (ensures 0 <= i /\ i <= Seq.length t ==>
                   Seq.length (sym_except c s (Seq.slice t 0 i)) <= Seq.length s + i)
  = if 0 <= i && i <= Seq.length t then sym_except_length_ c s (Seq.slice t 0 i)
