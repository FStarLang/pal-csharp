module Pulse.Lib.CSharp.SetInter

/// The intersection of two strictly sorted sets, as `SortedSet<T>.IntersectWith` merges it.
/// `inter c s t`: the elements of `t` that compare equal to some element of `s`, in `t`'s
/// order.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted

let rec occurs (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (y: a)
  : Tot bool (decreases Seq.length s) =
  if Seq.length s = 0 then false
  else O.compare c (Seq.head s) y = 0 || occurs c (Seq.tail s) y

let rec inter (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Tot (Seq.seq a) (decreases Seq.length t) =
  if Seq.length t = 0 then Seq.empty
  else if occurs c s (Seq.head t) then Seq.cons (Seq.head t) (inter c s (Seq.tail t))
  else inter c s (Seq.tail t)

let rec occurs_index (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (y: a)
  : Lemma (ensures occurs c s y <==> (exists (k: nat). k < Seq.length s /\ O.compare c (Seq.index s k) y == 0))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      occurs_index c (Seq.tail s) y;
      assert (forall (k: nat). 0 < k /\ k < Seq.length s ==> Seq.index (Seq.tail s) (k - 1) == Seq.index s k);
      assert (forall (k: nat). k < Seq.length s - 1 ==> Seq.index (Seq.tail s) k == Seq.index s (k + 1))
    end

let rec inter_ext (#a: Type0) (c: O.comparer a) (s1 s2 t: Seq.seq a)
  : Lemma (requires forall (k: nat). k < Seq.length t ==> occurs c s1 (Seq.index t k) == occurs c s2 (Seq.index t k))
          (ensures inter c s1 t == inter c s2 t)
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else begin
      assert (forall (k: nat). k < Seq.length t - 1 ==> Seq.index (Seq.tail t) k == Seq.index t (k + 1));
      inter_ext c s1 s2 (Seq.tail t)
    end

let suffix_cons (#a: Type0) (s: Seq.seq a) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures Seq.head (Seq.slice s i (Seq.length s)) == Seq.index s i /\
                   Seq.tail (Seq.slice s i (Seq.length s)) == Seq.slice s (i + 1) (Seq.length s))
  = Seq.lemma_eq_elim (Seq.tail (Seq.slice s i (Seq.length s))) (Seq.slice s (i + 1) (Seq.length s))

let trans_lt (#a: Type0) (c: O.comparer a) (x y z: a)
  : Lemma (requires O.compare c x y < 0 /\ O.compare c y z <= 0) (ensures O.compare c x z < 0)
  = O.compare_trans c x y z

let trans_le_lt (#a: Type0) (c: O.comparer a) (x y z: a)
  : Lemma (requires O.compare c x y <= 0 /\ O.compare c y z < 0) (ensures O.compare c x z < 0)
  = O.compare_trans c x y z

/// One step of the merge: the suffixes from `i` in `s` and `j` in `t`.
let inter_step (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t /\
                    0 <= i /\ i < Seq.length s /\ 0 <= j /\ j < Seq.length t)
          (ensures (let si = Seq.slice s i (Seq.length s) in
                    let tj = Seq.slice t j (Seq.length t) in
                    let si' = Seq.slice s (i + 1) (Seq.length s) in
                    let tj' = Seq.slice t (j + 1) (Seq.length t) in
                    let o = O.compare c (Seq.index s i) (Seq.index t j) in
                    inter c si tj ==
                    (if o < 0 then inter c si' tj
                     else if o = 0 then Seq.cons (Seq.index t j) (inter c si' tj')
                     else inter c si tj')))
  = let si = Seq.slice s i (Seq.length s) in
    let tj = Seq.slice t j (Seq.length t) in
    let si' = Seq.slice s (i + 1) (Seq.length s) in
    let tj' = Seq.slice t (j + 1) (Seq.length t) in
    let x = Seq.index s i in
    let y = Seq.index t j in
    suffix_cons s i; suffix_cons t j;
    let o = O.compare c x y in
    // occurs over si is x, or occurs over si'.
    assert (forall (z: a). occurs c si z == (O.compare c x z = 0 || occurs c si' z));
    if o < 0 then begin
      let l (k: nat{k < Seq.length tj}) : Lemma (occurs c si (Seq.index tj k) == occurs c si' (Seq.index tj k)) =
        assert (Seq.index tj k == Seq.index t (j + k));
        if k > 0 then trans_lt c x y (Seq.index t (j + k));
        O.compare_antisym c x (Seq.index tj k)
      in
      FStar.Classical.forall_intro l;
      inter_ext c si si' tj
    end else if o = 0 then begin
      let l (k: nat{k < Seq.length tj'}) : Lemma (occurs c si (Seq.index tj' k) == occurs c si' (Seq.index tj' k)) =
        assert (Seq.index tj' k == Seq.index t (j + 1 + k));
        O.compare_trans c x y (Seq.index t (j + 1 + k));
        O.compare_antisym c x (Seq.index tj' k)
      in
      FStar.Classical.forall_intro l;
      inter_ext c si si' tj'
    end else begin
      occurs_index c si y;
      let l (k: nat{k < Seq.length si}) : Lemma (O.compare c (Seq.index si k) y <> 0) =
        assert (Seq.index si k == Seq.index s (i + k));
        O.compare_antisym c x y;
        if k > 0 then (O.compare_antisym c x (Seq.index s (i + k)); trans_lt c y x (Seq.index s (i + k)); O.compare_antisym c y (Seq.index s (i + k)))
        else ()
      in
      FStar.Classical.forall_intro l
    end

/// Nothing of `t` from `j` on equals anything of `s` from `i` on, when `t[j]` is above `s`'s last.
let inter_above (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t /\
                    0 <= i /\ i <= Seq.length s /\ 0 <= j /\ j < Seq.length t /\ Seq.length s > 0 /\
                    O.compare c (Seq.index t j) (Seq.index s (Seq.length s - 1)) > 0)
          (ensures inter c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t)) == Seq.empty)
  = let si = Seq.slice s i (Seq.length s) in
    let tj = Seq.slice t j (Seq.length t) in
    let m = Seq.index s (Seq.length s - 1) in
    let rec go (u: Seq.seq a)
      : Lemma (requires forall (k: nat). k < Seq.length u ==> O.compare c m (Seq.index u k) < 0)
              (ensures inter c si u == Seq.empty) (decreases Seq.length u)
      = if Seq.length u = 0 then Seq.lemma_eq_elim (inter c si u) Seq.empty
        else begin
          let y = Seq.head u in
          occurs_index c si y;
          let l (k: nat{k < Seq.length si}) : Lemma (O.compare c (Seq.index si k) y <> 0) =
            assert (Seq.index si k == Seq.index s (i + k));
            O.compare_antisym c m y;
            if i + k < Seq.length s - 1 then trans_lt c (Seq.index s (i + k)) m y
          in
          FStar.Classical.forall_intro l;
          assert (forall (k: nat). k < Seq.length u - 1 ==> Seq.index (Seq.tail u) k == Seq.index u (k + 1));
          go (Seq.tail u)
        end
    in
    let l (k: nat{k < Seq.length tj}) : Lemma (O.compare c m (Seq.index tj k) < 0) =
      assert (Seq.index tj k == Seq.index t (j + k));
      O.compare_antisym c m (Seq.index t j);
      if k > 0 then trans_lt c m (Seq.index t j) (Seq.index t (j + k))
    in
    FStar.Classical.forall_intro l;
    go tj

let inter_nil_left (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires 0 <= j /\ j <= Seq.length t /\ i == Seq.length s)
          (ensures inter c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t)) == Seq.empty)
  = let rec go (u: Seq.seq a) : Lemma (ensures inter c Seq.empty u == Seq.empty) (decreases Seq.length u) =
      if Seq.length u = 0 then Seq.lemma_eq_elim (inter c Seq.empty u) Seq.empty else go (Seq.tail u)
    in
    Seq.lemma_eq_elim (Seq.slice s i (Seq.length s)) Seq.empty;
    go (Seq.slice t j (Seq.length t))

let inter_nil_right (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires j == Seq.length t)
          (ensures inter c s (Seq.slice t j (Seq.length t)) == Seq.empty)
  = Seq.lemma_eq_elim (inter c s (Seq.slice t j (Seq.length t))) Seq.empty

let inter_whole (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (inter c (Seq.slice s 0 (Seq.length s)) (Seq.slice t 0 (Seq.length t)) == inter c s t)
  = Seq.lemma_eq_elim (Seq.slice s 0 (Seq.length s)) s;
    Seq.lemma_eq_elim (Seq.slice t 0 (Seq.length t)) t

/// Each element of `inter c s t` is an element of `t`.
let rec inter_elems (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (ensures Seq.length (inter c s t) <= Seq.length t /\
                   (forall (k: nat). k < Seq.length (inter c s t) ==>
                      (exists (m: nat). m < Seq.length t /\ Seq.index (inter c s t) k == Seq.index t m)))
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else begin
      inter_elems c s (Seq.tail t);
      assert (forall (m: nat). m < Seq.length t - 1 ==> Seq.index (Seq.tail t) m == Seq.index t (m + 1));
      if occurs c s (Seq.head t) then begin
        let r = inter c s (Seq.tail t) in
        assert (forall (k: nat). 0 < k /\ k < Seq.length r + 1 ==> Seq.index (Seq.cons (Seq.head t) r) k == Seq.index r (k - 1))
      end
    end

/// The intersection with a strictly sorted `t` is strictly sorted.
let rec inter_sorted (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (requires S.strictly_sorted c t)
          (ensures S.strictly_sorted c (inter c s t) /\ Seq.length (inter c s t) <= Seq.length t)
          (decreases Seq.length t)
  = inter_elems c s t;
    if Seq.length t = 0 then ()
    else begin
      let u = Seq.tail t in
      assert (forall (m: nat). m < Seq.length u ==> Seq.index u m == Seq.index t (m + 1));
      inter_sorted c s u;
      if occurs c s (Seq.head t) then begin
        let r = inter c s u in
        inter_elems c s u;
        let h = Seq.head t in
        let l (k: nat{k < Seq.length r}) : Lemma (O.compare c h (Seq.index r k) < 0) =
          assert (exists (m: nat). m < Seq.length u /\ Seq.index r k == Seq.index u m)
        in
        FStar.Classical.forall_intro l;
        let w = Seq.cons h r in
        assert (forall (k: nat). 0 < k /\ k < Seq.length w ==> Seq.index w k == Seq.index r (k - 1));
        assert (Seq.index w 0 == h)
      end
    end

/// Where the merge stops: `s` is used up, `t` is used up, or `t[j]` is above `s`'s last.
let inter_done (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t /\
                    0 <= i /\ i <= Seq.length s /\ 0 <= j /\ j <= Seq.length t /\
                    (i == Seq.length s \/ j == Seq.length t \/
                     (Seq.length s > 0 /\ j < Seq.length t /\ O.compare c (Seq.index t j) (Seq.index s (Seq.length s - 1)) > 0)))
          (ensures inter c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t)) == Seq.empty)
  = if i = Seq.length s then inter_nil_left c s t i j
    else if j = Seq.length t then inter_nil_right c (Seq.slice s i (Seq.length s)) t i j
    else inter_above c s t i j

/// Nothing intersects an empty `s`.
let rec inter_left_empty (#a: Type0) (c: O.comparer a) (s t: Seq.seq a)
  : Lemma (ensures Seq.length s == 0 ==> inter c s t == Seq.empty)
          (decreases Seq.length t)
  = if Seq.length s = 0 && Seq.length t > 0 then inter_left_empty c s (Seq.tail t)

/// After the merge: the prefix collected is the whole intersection.
let inter_finish (#a: Type0) (c: O.comparer a) (s t: Seq.seq a) (i j: int) (p: Seq.seq a)
  : Lemma (requires S.strictly_sorted c s /\ S.strictly_sorted c t /\
                    0 <= i /\ i <= Seq.length s /\ 0 <= j /\ j <= Seq.length t /\
                    (i == Seq.length s \/ j == Seq.length t \/
                     (Seq.length s > 0 /\ j < Seq.length t /\ O.compare c (Seq.index t j) (Seq.index s (Seq.length s - 1)) > 0)) /\
                    Seq.append p (inter c (Seq.slice s i (Seq.length s)) (Seq.slice t j (Seq.length t))) == inter c s t)
          (ensures p == inter c s t)
  = inter_done c s t i j;
    Seq.append_empty_r p

/// Writing `x` at `k` extends the prefix `m[0..k)` by `x`, ahead of any rest `r`.
let push_prefix (#a: Type0) (m: Seq.seq a) (k: int) (x: a) (r: Seq.seq a)
  : Lemma (requires 0 <= k /\ k < Seq.length m)
          (ensures Seq.append (Seq.slice (Seq.upd m k x) 0 (k + 1)) r ==
                   Seq.append (Seq.slice m 0 k) (Seq.cons x r))
  = Seq.lemma_eq_elim (Seq.append (Seq.slice (Seq.upd m k x) 0 (k + 1)) r)
                      (Seq.append (Seq.slice m 0 k) (Seq.cons x r))
