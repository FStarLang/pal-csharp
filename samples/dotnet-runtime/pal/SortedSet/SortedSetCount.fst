module SortedSetCount

/// `SortedSet<T>.CheckUniqueAndUnfoundElements` as dotnet/runtime#133116 rewrites it: each item
/// of `other` is looked up by its breadth-first position in the tree (`InternalIndexOf`,
/// `SearchTree.heap_index`), and a bitmap over those positions, sized from a bound on the
/// tree's height, counts the distinct members found.
///
/// * `found`/`unfound`: what the method is to count, over the set's keys (in order) and the
///   items of `other` enumerated so far. `ok` is the range a view admits (`in_range`), or every
///   key for a set (`all_ok`).
/// * `index_of`: the position the method looks an item up at, or -1.
/// * `phit`: whether some item enumerated so far has position `p`, what the bitmap records.
/// * `step`: one item, as the loop's body takes it.
/// * The bound: `heap_index` is below `2^height`, and a red-black tree of `n` nodes has height
///   at most `2 * log2(n + 1)` (`red_black_height`); a view's root lies `range_depth` below the
///   set's root (`range_root_height`).
///
/// Nothing here is trusted: it is proved from `SearchTree`, `Sorted` and `Order`.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module A = Pulse.Lib.CSharp.Arith
module RW = Pulse.Lib.CSharp.RangeWalk

(* ---------------------------------------------------------------------------------- *)
(* Equivalent items                                                                    *)

let equiv_sign (#a: Type0) (c: O.comparer a) (x y v: a)
  : Lemma (requires O.compare c x y == 0)
          (ensures (O.compare c x v < 0 <==> O.compare c y v < 0) /\
                   (O.compare c x v == 0 <==> O.compare c y v == 0) /\
                   (O.compare c v x < 0 <==> O.compare c v y < 0) /\
                   (O.compare c v x == 0 <==> O.compare c v y == 0))
  = O.compare_antisym c x y;
    O.compare_antisym c x v;
    O.compare_antisym c y v;
    FStar.Classical.move_requires (O.compare_trans c y x) v;
    FStar.Classical.move_requires (O.compare_trans c x y) v;
    FStar.Classical.move_requires (O.compare_trans c v x) y;
    FStar.Classical.move_requires (O.compare_trans c v y) x

let equiv_sym (#a: Type0) (c: O.comparer a) (x y: a)
  : Lemma (requires O.compare c x y == 0) (ensures O.compare c y x == 0)
  = O.compare_antisym c x y

let equiv_trans (#a: Type0) (c: O.comparer a) (x y z: a)
  : Lemma (requires O.compare c x y == 0 /\ O.compare c y z == 0) (ensures O.compare c x z == 0)
  = equiv_sign c x y z

/// A range admits an item exactly when it admits every equivalent one.
let in_range_equiv (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (x y: a)
  : Lemma (requires O.compare c x y == 0)
          (ensures ST.in_range c lo hi la ua x == ST.in_range c lo hi la ua y)
  = equiv_sign c x y lo; equiv_sign c x y hi

let rec lower_bound_equiv (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x y: a)
  : Lemma (requires O.compare c x y == 0)
          (ensures S.lower_bound c s x == S.lower_bound c s y)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      equiv_sign c x y (Seq.head s);
      lower_bound_equiv c (Seq.tail s) x y
    end

let key_index_equiv (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x y: a)
  : Lemma (requires O.compare c x y == 0)
          (ensures S.key_index c s x == S.key_index c s y)
  = lower_bound_equiv c s x y;
    let lb = S.lower_bound c s x in
    if lb < Seq.length s then equiv_sign c x y (Seq.index s lb)

/// In a strictly sorted sequence, an element's key index is its position.
let key_index_index (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (i: nat)
  : Lemma (requires S.strictly_sorted c s /\ i < Seq.length s)
          (ensures S.key_index c s (Seq.index s i) == i)
  = let x = Seq.index s i in
    let s1 = Seq.slice s 0 i in
    let s2 = Seq.slice s i (Seq.length s) in
    Seq.lemma_split s i;
    ST.lower_bound_all_below c s1 x;
    ST.lower_bound_all_above c s2 x;
    ST.lower_bound_append c s1 s2 x

/// In a strictly sorted sequence, the item equivalent to `x` is at `x`'s key index, and
/// there is none if that is negative.
let key_index_unique (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x: a) (i: nat)
  : Lemma (requires S.strictly_sorted c s /\ i < Seq.length s)
          (ensures (O.compare c x (Seq.index s i) == 0) <==> S.key_index c s x == i)
  = key_index_index c s i;
    if O.compare c x (Seq.index s i) = 0 then key_index_equiv c s x (Seq.index s i)
    else begin
      let k = S.key_index c s x in
      if k = i then begin
        assert (O.compare c (Seq.index s k) x == 0);
        O.compare_antisym c (Seq.index s k) x
      end
    end

(* ---------------------------------------------------------------------------------- *)
(* Breadth-first positions: the search for two items ends at one position exactly when  *)
(* they are equivalent.                                                                 *)

/// `q` is `p` or one of its ancestors in the implicit binary heap numbering.
let rec anc (q p: nat) : Tot bool (decreases p) =
  p = q || (p > q && anc q ((p - 1) / 2))

let rec anc_trans (a b p: nat)
  : Lemma (requires anc a b /\ anc b p) (ensures anc a p) (decreases p)
  = if p = b then () else anc_trans a b ((p - 1) / 2)

let rec anc_chain (q q' p: nat)
  : Lemma (requires anc q p /\ anc q' p /\ q < q') (ensures anc q q') (decreases p)
  = if q' = p then () else anc_chain q q' ((p - 1) / 2)

let anc_children (k p: nat)
  : Lemma ((anc (2 * k + 1) p ==> anc k p /\ p > k) /\
           (anc (2 * k + 2) p ==> anc k p /\ p > k) /\
           ~(anc (2 * k + 1) p /\ anc (2 * k + 2) p))
  = assert (anc k (2 * k + 1));
    assert (anc k (2 * k + 2));
    FStar.Classical.move_requires (anc_trans k (2 * k + 1)) p;
    FStar.Classical.move_requires (anc_trans k (2 * k + 2)) p;
    FStar.Classical.move_requires (anc_chain (2 * k + 1) (2 * k + 2)) p

let rec heap_index_anc (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a) (k: nat)
  : Lemma (ensures (let p = ST.heap_index c t x k in p >= 0 ==> anc k p))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      let p = ST.heap_index c t x k in
      if o = 0 then ()
      else if o < 0 then begin
        heap_index_anc c l x (2 * k + 1);
        if p >= 0 then anc_children k p
      end
      else begin
        heap_index_anc c r x (2 * k + 2);
        if p >= 0 then anc_children k p
      end

/// Two searches ending at one position ended at one node: the items are equivalent.
let rec heap_index_inj (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x y: a) (k: nat)
  : Lemma (requires ST.heap_index c t x k >= 0 /\ ST.heap_index c t x k == ST.heap_index c t y k)
          (ensures O.compare c x y == 0)
          (decreases t)
  = match t with
    | T.Branch l (v, _) r ->
      let ox = O.compare c x v in
      let oy = O.compare c y v in
      let p = ST.heap_index c t x k in
      heap_index_anc c l x (2 * k + 1);
      heap_index_anc c r x (2 * k + 2);
      heap_index_anc c l y (2 * k + 1);
      heap_index_anc c r y (2 * k + 2);
      anc_children k p;
      if ox = 0 && oy = 0 then begin equiv_sym c y v; equiv_trans c x v y end
      else if ox < 0 && oy < 0 then heap_index_inj c l x y (2 * k + 1)
      else if ox > 0 && oy > 0 then heap_index_inj c r x y (2 * k + 2)
      else ()

/// Equivalent items are searched for along one path.
let rec heap_index_equiv (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x y: a) (k: int)
  : Lemma (requires O.compare c x y == 0)
          (ensures ST.heap_index c t x k == ST.heap_index c t y k)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, _) r ->
      equiv_sign c x y v;
      heap_index_equiv c l x y (2 * k + 1);
      heap_index_equiv c r x y (2 * k + 2)

(* ---------------------------------------------------------------------------------- *)
(* What the method counts                                                              *)

/// `s` without its last item.
let init (#a: Type0) (s: Seq.seq a{Seq.length s > 0}) : Seq.seq a = Seq.slice s 0 (Seq.length s - 1)

/// Some item of `s` is equivalent to `y`.
let rec hit (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (y: a) : Tot bool (decreases Seq.length s) =
  Seq.length s > 0 && (O.compare c (Seq.last s) y = 0 || hit c (init s) y)

/// The keys among `ks[0..n)` that `ok` admits and some item of `s` is equivalent to.
let rec found_upto (#a: Type0) (c: O.comparer a) (ok: a -> bool) (ks s: Seq.seq a) (n: nat{n <= Seq.length ks})
  : Tot nat (decreases n)
  = if n = 0 then 0
    else found_upto c ok ks s (n - 1) + (if ok (Seq.index ks (n - 1)) && hit c s (Seq.index ks (n - 1)) then 1 else 0)

/// The distinct keys of `ks` that `ok` admits and that `s` holds (up to equivalence).
let found (#a: Type0) (c: O.comparer a) (ok: a -> bool) (ks s: Seq.seq a) : nat =
  found_upto c ok ks s (Seq.length ks)

/// The items of `s` that are not a key of `ks` that `ok` admits.
let rec unfound (#a: Type0) (c: O.comparer a) (ok: a -> bool) (ks s: Seq.seq a) : Tot nat (decreases Seq.length s) =
  if Seq.length s = 0 then 0
  else unfound c ok ks (init s) + (if ok (Seq.last s) && S.key_index c ks (Seq.last s) >= 0 then 0 else 1)

let all_ok (#a: Type0) (x: a) : bool = true

/// The set's counts: every key is admitted.
let found_all (#a: Type0) (c: O.comparer a) (ks s: Seq.seq a) : nat = found c all_ok ks s
let unfound_all (#a: Type0) (c: O.comparer a) (ks s: Seq.seq a) : nat = unfound c all_ok ks s

/// A view's counts: the keys within its range.
let found_range (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (ks s: Seq.seq a) : nat =
  found c (ST.in_range c lo hi la ua) ks s
let unfound_range (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (ks s: Seq.seq a) : nat =
  unfound c (ST.in_range c lo hi la ua) ks s

(* ---------------------------------------------------------------------------------- *)
(* The positions the method looks items up at                                          *)

/// The position of `x` in `tr` if `ok` admits it, or -1.
let index_of (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (x: a) : int =
  if ok x then ST.heap_index c tr x 0 else -1

/// Some item of `s` is at position `p`: the bitmap's bit `p`.
let rec phit (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (s: Seq.seq a) (p: int)
  : Tot bool (decreases Seq.length s)
  = Seq.length s > 0 && (index_of c ok tr (Seq.last s) = p || phit c ok tr (init s) p)

/// What the method needs of `ok`, `tr` and the keys `ks`: `ok` respects equivalence, `ks` is
/// strictly sorted, and an admitted item is found in `tr` exactly when it is a key.
let lookup_ok (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (ks: Seq.seq a) : prop =
  S.strictly_sorted c ks /\
  (forall (x y: a). O.compare c x y == 0 ==> ok x == ok y) /\
  (forall (x: a). ok x ==> (ST.contains c tr x <==> S.key_index c ks x >= 0))

let ok_equiv (#a: Type0) (c: O.comparer a) (ok: a -> bool) (x y: a)
  : Lemma (requires (forall (x y: a). O.compare c x y == 0 ==> ok x == ok y) /\ O.compare c x y == 0)
          (ensures ok x == ok y)
  = ()

/// For `x` at position `p >= 0`: an item is at `p` exactly when it is equivalent to `x`.
let pos_equiv (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (ks: Seq.seq a) (x y: a)
  : Lemma (requires lookup_ok c ok tr ks /\ index_of c ok tr x >= 0)
          (ensures index_of c ok tr y == index_of c ok tr x <==> O.compare c y x == 0)
  = if O.compare c y x = 0 then begin
      ok_equiv c ok y x;
      heap_index_equiv c tr y x 0
    end
    else if index_of c ok tr y = index_of c ok tr x then heap_index_inj c tr y x 0

let rec hit_phit (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (ks: Seq.seq a) (s: Seq.seq a) (x: a)
  : Lemma (requires lookup_ok c ok tr ks /\ index_of c ok tr x >= 0)
          (ensures hit c s x == phit c ok tr s (index_of c ok tr x))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      pos_equiv c ok tr ks x (Seq.last s);
      hit_phit c ok tr ks (init s) x
    end

let init_snoc (#a: Type0) (s: Seq.seq a) (x: a)
  : Lemma (Seq.length (Seq.snoc s x) > 0 /\ init (Seq.snoc s x) == s /\ Seq.last (Seq.snoc s x) == x)
  = Seq.lemma_eq_intro (init (Seq.snoc s x)) s

let hit_snoc (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x y: a)
  : Lemma (hit c (Seq.snoc s x) y == (O.compare c x y = 0 || hit c s y))
  = init_snoc s x

/// Taking `x` changes the count only at `x`'s key, and only if no earlier item matched it.
let rec found_upto_snoc (#a: Type0) (c: O.comparer a) (ok: a -> bool) (ks s: Seq.seq a) (x: a) (n: nat{n <= Seq.length ks})
  : Lemma (requires S.strictly_sorted c ks /\ (forall (x y: a). O.compare c x y == 0 ==> ok x == ok y))
          (ensures (let i = S.key_index c ks x in
                    found_upto c ok ks (Seq.snoc s x) n ==
                    found_upto c ok ks s n +
                      (if ok x && 0 <= i && i < n && not (hit c s (Seq.index ks i)) then 1 else 0)))
          (decreases n)
  = if n = 0 then ()
    else begin
      found_upto_snoc c ok ks s x (n - 1);
      let k = Seq.index ks (n - 1) in
      hit_snoc c s x k;
      key_index_unique c ks x (n - 1);
      if O.compare c x k = 0 then ok_equiv c ok x k
    end

/// One item of `other`, as the loop takes it: what it adds to the counts and to the bitmap.
let step (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (ks: Seq.seq a) (s: Seq.seq a) (x: a)
  : Lemma (requires lookup_ok c ok tr ks)
          (ensures (let p = index_of c ok tr x in
                    let s' = Seq.snoc s x in
                    unfound c ok ks s' == unfound c ok ks s + (if p >= 0 then 0 else 1) /\
                    found c ok ks s' == found c ok ks s + (if p >= 0 && not (phit c ok tr s p) then 1 else 0) /\
                    (forall (q: int). phit c ok tr s' q == (q = p || phit c ok tr s q))))
  = init_snoc s x;
    found_upto_snoc c ok ks s x (Seq.length ks);
    let p = index_of c ok tr x in
    let i = S.key_index c ks x in
    if p >= 0 then begin
      key_index_index c ks i;
      assert (O.compare c (Seq.index ks i) x == 0);
      key_index_unique c ks x i;
      ok_equiv c ok x (Seq.index ks i);
      hit_phit c ok tr ks s (Seq.index ks i);
      pos_equiv c ok tr ks x (Seq.index ks i)
    end

let found_empty (#a: Type0) (c: O.comparer a) (ok: a -> bool) (ks: Seq.seq a) (s: Seq.seq a)
  : Lemma (requires Seq.length s == 0) (ensures found c ok ks s == 0 /\ unfound c ok ks s == 0)
  = let rec aux (n: nat{n <= Seq.length ks}) : Lemma (ensures found_upto c ok ks s n == 0) (decreases n)
      = if n = 0 then () else aux (n - 1) in
    aux (Seq.length ks)

let phit_empty (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (s: Seq.seq a) (p: int)
  : Lemma (requires Seq.length s == 0) (ensures phit c ok tr s p == false)
  = ()

/// With no keys, every item is unfound.
let rec unfound_no_keys (#a: Type0) (c: O.comparer a) (ok: a -> bool) (ks s: Seq.seq a)
  : Lemma (requires Seq.length ks == 0)
          (ensures unfound c ok ks s == Seq.length s /\ found c ok ks s == 0)
          (decreases Seq.length s)
  = if Seq.length s = 0 then () else unfound_no_keys c ok ks (init s)

(* ---------------------------------------------------------------------------------- *)
(* The set and its views meet `lookup_ok`                                              *)

let all_ok_lookup (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b))
  : Lemma (requires S.strictly_sorted c (ST.keys t)) (ensures lookup_ok c all_ok t (ST.keys t))
  = let aux (x: a) : Lemma (ST.contains c t x <==> S.key_index c (ST.keys t) x >= 0)
      = ST.contains_keys c t x in
    FStar.Classical.forall_intro aux

let range_lookup (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (requires S.strictly_sorted c (ST.keys t))
          (ensures lookup_ok c (ST.in_range c lo hi la ua) (ST.range_root c t lo hi la ua) (ST.keys t))
  = let aux (x: a)
      : Lemma (ST.in_range c lo hi la ua x ==>
               (ST.contains c (ST.range_root c t lo hi la ua) x <==> S.key_index c (ST.keys t) x >= 0))
      = ST.contains_keys c t x;
        if ST.in_range c lo hi la ua x then ST.range_root_contains c t lo hi la ua x in
    FStar.Classical.forall_intro aux;
    let eq (x y: a) : Lemma (O.compare c x y == 0 ==> ST.in_range c lo hi la ua x == ST.in_range c lo hi la ua y)
      = FStar.Classical.move_requires (in_range_equiv c lo hi la ua x) y in
    FStar.Classical.forall_intro_2 eq

(* ---------------------------------------------------------------------------------- *)
(* The bound: positions are below 2^height, and the height is bounded                  *)

let pos_bound (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (x: a)
  : Lemma (index_of c ok tr x < pow2 (T.height tr) - 1)
  = ST.heap_index_bound c tr x

let rec rb_height (#a: Type0) (t: T.tree (a & bool))
  : Lemma (requires ST.rb t)
          (ensures T.height t <= 2 * ST.black_height t + (if ST.is_red t then 1 else 0) /\
                   pow2 (ST.black_height t) <= T.size t + 1)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (_, red) r ->
      rb_height l; rb_height r;
      if not red then FStar.Math.Lemmas.pow2_double_sum (ST.black_height l)

let rec log2_ge (b: nat) (m: Prims.pos)
  : Lemma (requires pow2 b <= m) (ensures b <= A.log2_nat m) (decreases b)
  = if b = 0 then ()
    else begin
      FStar.Math.Lemmas.pow2_double_mult (b - 1);
      log2_ge (b - 1) (m / 2)
    end

/// A red-black tree (black root) of `n` nodes has height at most `2 * floor(log2(n + 1))`:
/// the bound `GetApproximateMaxHeight` takes.
let red_black_height (#a: Type0) (t: T.tree (a & bool))
  : Lemma (requires ST.red_black t) (ensures T.height t <= 2 * A.log2_nat (T.size t + 1))
  = rb_height t; log2_ge (ST.black_height t) (T.size t + 1)

/// The depth of the node a range search stops at: `FindRange`'s `level`.
let rec range_depth (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Tot nat (decreases t)
  = match t with
    | T.Leaf -> 0
    | T.Branch l (v, _) r ->
      if la && O.compare c lo v > 0 then 1 + range_depth c r lo hi la ua
      else if ua && O.compare c hi v < 0 then 1 + range_depth c l lo hi la ua
      else 0

/// The depth is at most the tree's size: `FindRange`'s `level++` cannot overflow.
let rec range_depth_le_size (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (ensures range_depth c t lo hi la ua <= T.size t) (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ r -> range_depth_le_size c l lo hi la ua; range_depth_le_size c r lo hi la ua

let rec range_root_height (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (ensures T.height (ST.range_root c t lo hi la ua) + range_depth c t lo hi la ua <= T.height t)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, _) r ->
      if la && O.compare c lo v > 0 then range_root_height c r lo hi la ua
      else if ua && O.compare c hi v < 0 then range_root_height c l lo hi la ua
      else ()

(* ---------------------------------------------------------------------------------- *)
(* The method's loop, over the range `in_range c lo hi la ua`                          *)
(*                                                                                     *)
(* A set is the range with neither bound active (`in_range` is then always true, and   *)
(* `range_root` the whole tree); a view is its own range. So one invariant serves the  *)
(* method's body at the set and at its replica at a view (R32.13).                     *)

/// The bitmap `m` records the positions of the items of `s`.
let marks (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (m: Seq.seq bool) (s: Seq.seq a) : prop =
  forall (p: nat). {:pattern (Seq.index m p)} p < Seq.length m ==> Seq.index m p == phit c ok tr s p

/// What the method relies on of the tree `tr` it searches and the keys `ks` it counts.
let lookup (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a) : prop =
  lookup_ok c (ST.in_range c lo hi la ua) tr ks

/// The loop's invariant after the first `i` items of `all`.
let loop_inv (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
             (m: Seq.seq bool) (all: Seq.seq a) (i: int) (uniq unf: int) : prop =
  0 <= i /\ i <= Seq.length all /\
  (let ok = ST.in_range c lo hi la ua in
   let s = Seq.slice all 0 i in
   marks c ok tr m s /\ uniq == found c ok ks s /\ unf == unfound c ok ks s)

/// The position the method's loop looks `x` up at (with the fix: -1 outside the range).
let range_index (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (tr: T.tree (a & b)) (x: a) : int =
  index_of c (ST.in_range c lo hi la ua) tr x

/// Every position in `tr` is below `lim`.
let fits (#a #b: Type0) (c: O.comparer a) (tr: T.tree (a & b)) (lim: int) : prop =
  forall (x: a). {:pattern (ST.heap_index c tr x 0)} ST.heap_index c tr x 0 < lim

/// `1 << h` for the bitmap's length, at a height of at most 12: no overflow, and `2^h`.
let shift_one (h: int)
  : Lemma (requires 0 <= h /\ h <= 12)
          (ensures pow2 h <= 4096 /\
                   (forall (x: FStar.Int32.t). {:pattern (FStar.Int.Cast.int32_to_uint32 x)}
                      FStar.Int32.v x == h ==>
                      FStar.UInt32.v (FStar.Int.Cast.int32_to_uint32 x) == h /\
                      1 * pow2 h <= FStar.Int.max_int 32 /\
                      FStar.Int32.v (FStar.Int32.shift_left 1l (FStar.Int.Cast.int32_to_uint32 x)) == pow2 h))
  = FStar.Math.Lemmas.pow2_le_compat 12 h;
    assert_norm (pow2 12 == 4096);
    assert_norm (pow2 32 == 4294967296);
    FStar.Math.Lemmas.small_mod (pow2 h) (pow2 32)

let fits_pow2 (#a #b: Type0) (c: O.comparer a) (tr: T.tree (a & b)) (h: int)
  : Lemma (requires 0 <= h /\ T.height tr <= h) (ensures fits c tr (pow2 h))
  = let aux (x: a) : Lemma (ST.heap_index c tr x 0 < pow2 h)
      = pos_bound c all_ok tr x; FStar.Math.Lemmas.pow2_le_compat h (T.height tr) in
    FStar.Classical.forall_intro aux

/// With neither bound active, the range admits everything and its root is the tree.
let range_off (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (x: a)
  : Lemma (ST.in_range c lo hi false false x == true /\ ST.range_root c t lo hi false false == t)
  = ()

/// The set (`la = ua = false`) or a view, whose root is the range search's stop in the
/// set's tree `t` and whose keys are the set's.
let lookup_intro (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (requires S.strictly_sorted c (ST.keys t))
          (ensures lookup c lo hi la ua (ST.range_root c t lo hi la ua) (ST.keys t) /\
                   (not la /\ not ua ==> ST.range_root c t lo hi la ua == t))
  = range_lookup c t lo hi la ua

let marks_create (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (n: nat) (s: Seq.seq a)
  : Lemma (requires Seq.length s == 0) (ensures marks c ok tr (Seq.create n false) s)
  = ()

/// Before the loop: no item taken, a fresh bitmap.
let loop_start (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
               (m: Seq.seq bool) (all: Seq.seq a)
  : Lemma (requires (forall (p: nat). p < Seq.length m ==> Seq.index m p == false))
          (ensures loop_inv c lo hi la ua tr ks m all 0 0 0)
  = let s = Seq.slice all 0 0 in
    found_empty c (ST.in_range c lo hi la ua) ks s

let slice_snoc (#a: Type0) (all: Seq.seq a) (i: nat)
  : Lemma (requires i < Seq.length all)
          (ensures Seq.slice all 0 (i + 1) == Seq.snoc (Seq.slice all 0 i) (Seq.index all i))
  = Seq.lemma_eq_intro (Seq.slice all 0 (i + 1)) (Seq.snoc (Seq.slice all 0 i) (Seq.index all i))

let rec unfound_mono (#a: Type0) (c: O.comparer a) (ok: a -> bool) (ks: Seq.seq a) (all: Seq.seq a) (i: nat)
  : Lemma (requires i <= Seq.length all)
          (ensures unfound c ok ks (Seq.slice all 0 i) <= unfound c ok ks all)
          (decreases (Seq.length all - i))
  = if i = Seq.length all then Seq.lemma_eq_intro (Seq.slice all 0 i) all
    else begin
      unfound_mono c ok ks all (i + 1);
      slice_snoc all i;
      init_snoc (Seq.slice all 0 i) (Seq.index all i)
    end

/// After the loop: it took every item, or it stopped at an unfound one.
let loop_done (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
              (m: Seq.seq bool) (all: Seq.seq a) (i: int) (uniq unf: int)
  : Lemma (requires loop_inv c lo hi la ua tr ks m all i uniq unf /\ (i == Seq.length all \/ unf > 0))
          (ensures (let ok = ST.in_range c lo hi la ua in
                    (unf > 0) == (unfound c ok ks all > 0) /\
                    (i == Seq.length all ==> uniq == found c ok ks all /\ unf == unfound c ok ks all)))
  = unfound_mono c (ST.in_range c lo hi la ua) ks all i;
    if i = Seq.length all then Seq.lemma_eq_intro (Seq.slice all 0 i) all

/// No key within the range: every item is unfound, none found.
let rec filter_none (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (ks: Seq.seq a) (j: nat)
  : Lemma (requires Seq.length (RW.filter c lo hi la ua ks) == 0 /\ j < Seq.length ks)
          (ensures not (ST.in_range c lo hi la ua (Seq.index ks j)))
          (decreases j)
  = if j = 0 then () else filter_none c lo hi la ua (Seq.tail ks) (j - 1)

let rec empty_range_counts (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (ks s: Seq.seq a)
  : Lemma (requires S.strictly_sorted c ks /\ Seq.length (RW.filter c lo hi la ua ks) == 0)
          (ensures unfound c (ST.in_range c lo hi la ua) ks s == Seq.length s /\
                   found c (ST.in_range c lo hi la ua) ks s == 0)
          (decreases Seq.length s)
  = let ok = ST.in_range c lo hi la ua in
    let rec f (n: nat{n <= Seq.length ks}) : Lemma (found_upto c ok ks s n == 0) (decreases n)
      = if n = 0 then () else (filter_none c lo hi la ua ks (n - 1); f (n - 1)) in
    f (Seq.length ks);
    if Seq.length s = 0 then ()
    else begin
      empty_range_counts c lo hi la ua ks (init s);
      let x = Seq.last s in
      let i = S.key_index c ks x in
      if i >= 0 then begin
        key_index_index c ks i;
        filter_none c lo hi la ua ks i;
        in_range_equiv c lo hi la ua x (Seq.index ks i)
      end
    end

/// The set's counts are the range's with neither bound active.
let rec counts_off (#a: Type0) (c: O.comparer a) (lo hi: a) (ks s: Seq.seq a)
  : Lemma (ensures unfound c (ST.in_range c lo hi false false) ks s == unfound_all c ks s /\
                   found c (ST.in_range c lo hi false false) ks s == found_all c ks s)
          (decreases Seq.length s)
  = let rec f (n: nat{n <= Seq.length ks})
      : Lemma (found_upto c (ST.in_range c lo hi false false) ks s n == found_upto c all_ok ks s n) (decreases n)
      = if n = 0 then () else f (n - 1) in
    f (Seq.length ks);
    if Seq.length s = 0 then () else counts_off c lo hi ks (init s)

/// `BitOperations.RoundUpToPowerOf2(uint)`: the least power of two at least `x`, or 0 for 0
/// and above `2^31`. Only the growth branch the proof shows dead calls it.
let rec round_up_from (k: nat{k <= 31}) (v: nat) : Tot (n: nat{n <= pow2 31}) (decreases (31 - k)) =
  FStar.Math.Lemmas.pow2_le_compat 31 k;
  if k = 31 || pow2 k >= v then pow2 k else round_up_from (k + 1) v

let round_up_pow2 (x: FStar.UInt32.t) : FStar.UInt32.t =
  let v = FStar.UInt32.v x in
  if v = 0 || v > pow2 31 then 0ul else FStar.UInt32.uint_to_t (round_up_from 0 v)

/// The method's early exit: no key within the range (for the set, no key at all).
let empty_counts (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (ks s: Seq.seq a)
  : Lemma (requires S.strictly_sorted c ks /\ (Seq.length ks == 0 \/ Seq.length (RW.filter c lo hi la ua ks) == 0))
          (ensures unfound_range c lo hi la ua ks s == Seq.length s /\ found_range c lo hi la ua ks s == 0)
  = if Seq.length ks = 0 then unfound_no_keys c (ST.in_range c lo hi la ua) ks s
    else empty_range_counts c lo hi la ua ks s

/// After the loop: it stopped at an unfound item (`stopped`), or it took every item.
let loop_end (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
             (m: Seq.seq bool) (all: Seq.seq a) (uniq unf: int) (stopped: bool)
  : Lemma (requires (stopped ==> unf > 0 /\ unfound_range c lo hi la ua ks all > 0) /\
                    (not stopped ==> loop_inv c lo hi la ua tr ks m all (Seq.length all) uniq unf))
          (ensures (unf > 0) == (unfound_range c lo hi la ua ks all > 0) /\
                   (not stopped ==> uniq == found_range c lo hi la ua ks all /\ unf == unfound_range c lo hi la ua ks all))
  = if not stopped then loop_done c lo hi la ua tr ks m all (Seq.length all) uniq unf

(* ---------------------------------------------------------------------------------- *)
(* The loop over any admitting predicate `ok`, and bounds given as sequences           *)
(*                                                                                     *)
(* The method's body is checked at the set and at its replica at a view (R32.13), and  *)
(* names the range through `[Spec]` members the view overrides (R37.7). A set has no    *)
(* bound and so no key to name one by: its bounds are empty sequences, a view's are    *)
(* `one _min` and `one _max`.                                                           *)

let none (a: Type0) : Seq.seq a = Seq.empty
let one (#a: Type0) (x: a) : Seq.seq a = Seq.create 1 x

let has_bound (#a: Type0) (los his: Seq.seq a) (la ua: bool) : bool =
  (la || ua) && (Seq.length los > 0 || Seq.length his > 0)

let pk (#a: Type0) (s1 s2: Seq.seq a)
  : Pure a (requires Seq.length s1 > 0 \/ Seq.length s2 > 0) (ensures fun _ -> True)
  = if Seq.length s1 > 0 then Seq.index s1 0 else Seq.index s2 0

let ok_s (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) : a -> bool =
  if has_bound los his la ua then ST.in_range c (pk los his) (pk his los) la ua else all_ok

/// `ok_s` applied to its bounds only is a function, which SMT does not unfold.
let ok_s_def (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
  : Lemma (ok_s c los his la ua ==
           (if has_bound los his la ua then ST.in_range c (pk los his) (pk his los) la ua else all_ok))
          [SMTPat (ok_s c los his la ua)]
  = assert (ok_s c los his la ua ==
            (if has_bound los his la ua then ST.in_range c (pk los his) (pk his los) la ua else all_ok))
      by (FStar.Tactics.V2.norm [delta_only [`%ok_s]]; FStar.Tactics.V2.trefl ())

let root_s (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (los his: Seq.seq a) (la ua: bool) : T.tree (a & b) =
  if has_bound los his la ua then ST.range_root c t (pk los his) (pk his los) la ua else t

let bounded (#a: Type0) (los his: Seq.seq a) (la ua: bool) : prop =
  (la ==> Seq.length los > 0) /\ (ua ==> Seq.length his > 0)

/// A view's bound, pinned across a loop as `one _min == old (one _min)`, is the bound itself.
let one_inj (#a: Type0) (x y: a)
  : Lemma (requires one x == one y) (ensures x == y) [SMTPat (one x); SMTPat (one y)]
  = assert (Seq.index (one x) 0 == x); assert (Seq.index (one y) 0 == y)

let pk_one (#a: Type0) (x y: a)
  : Lemma (pk (one x) (one y) == x) [SMTPat (pk (one x) (one y))]
  = ()

let one_bounded (#a: Type0) (x y: a) (la ua: bool)
  : Lemma (bounded (one x) (one y) la ua) [SMTPat (bounded (one x) (one y) la ua)]
  = ()

let root_one (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (root_s c t (one lo) (one hi) la ua == ST.range_root c t lo hi la ua)
          [SMTPat (root_s c t (one lo) (one hi) la ua)]
  = if not (la || ua) then range_off c t lo hi lo

let found_s (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (ks s: Seq.seq a) : nat =
  found c (ok_s c los his la ua) ks s
let unfound_s (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (ks s: Seq.seq a) : nat =
  unfound c (ok_s c los his la ua) ks s

let lookup_s (#a #b: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a) : prop =
  lookup_ok c (ok_s c los his la ua) tr ks

let loop_inv_g (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
               (m: Seq.seq bool) (all: Seq.seq a) (i: int) (uniq unf: int) : prop =
  0 <= i /\ i <= Seq.length all /\
  (let s = Seq.slice all 0 i in
   marks c ok tr m s /\ uniq == found c ok ks s /\ unf == unfound c ok ks s)

let loop_inv_s (#a #b: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
               (m: Seq.seq bool) (all: Seq.seq a) (i: int) (uniq unf: int) : prop =
  loop_inv_g c (ok_s c los his la ua) tr ks m all i uniq unf

/// The position the loop is to mark for `x`: -1 outside the range.
let index_s (#a #b: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (tr: T.tree (a & b)) (x: a) : int =
  index_of c (ok_s c los his la ua) tr x

let lookup_intro_s (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (los his: Seq.seq a) (la ua: bool)
  : Lemma (requires S.strictly_sorted c (ST.keys t) /\ bounded los his la ua)
          (ensures lookup_s c los his la ua (root_s c t los his la ua) (ST.keys t) /\
                   (not la /\ not ua ==> root_s c t los his la ua == t /\ ok_s c los his la ua == all_ok))
  = if has_bound los his la ua then range_lookup c t (pk los his) (pk his los) la ua
    else begin
      assert (ok_s c los his la ua == all_ok);
      assert (root_s c t los his la ua == t);
      all_ok_lookup c t
    end

let loop_start_s (#a #b: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
                 (m: Seq.seq bool) (all: Seq.seq a)
  : Lemma (requires (forall (p: nat). p < Seq.length m ==> Seq.index m p == false))
          (ensures loop_inv_s c los his la ua tr ks m all 0 0 0)
  = found_empty c (ok_s c los his la ua) ks (Seq.slice all 0 0)

let loop_step_g (#a #b: Type0) (c: O.comparer a) (ok: a -> bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
                (m: Seq.seq bool) (all: Seq.seq a) (i: int) (uniq unf: int)
  : Lemma (requires lookup_ok c ok tr ks /\ loop_inv_g c ok tr ks m all i uniq unf /\
                    i < Seq.length all /\ index_of c ok tr (Seq.index all i) < Seq.length m)
          (ensures (let p = index_of c ok tr (Seq.index all i) in
                    (p >= 0 /\ not (Seq.index m p) ==> loop_inv_g c ok tr ks (Seq.upd m p true) all (i + 1) (uniq + 1) unf) /\
                    (p >= 0 /\ Seq.index m p ==> loop_inv_g c ok tr ks m all (i + 1) uniq unf) /\
                    (p < 0 ==> loop_inv_g c ok tr ks m all (i + 1) uniq (unf + 1))))
  = let x = Seq.index all i in
    let s = Seq.slice all 0 i in
    slice_snoc all i;
    step c ok tr ks s x;
    let p = index_of c ok tr x in
    if p >= 0 then begin
      assert (Seq.index m p == phit c ok tr s p);
      let m' = Seq.upd m p true in
      let aux (q: nat) : Lemma (q < Seq.length m' ==> Seq.index m' q == phit c ok tr (Seq.snoc s x) q) = () in
      FStar.Classical.forall_intro aux
    end

/// One item, `all[i]`: the invariant after the body's update, in each of its three
/// branches, when the body marks position `index_s` (-1 outside the range).
let loop_step_s (#a #b: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
                (m: Seq.seq bool) (all: Seq.seq a) (i: int) (uniq unf: int)
  : Lemma (requires lookup_s c los his la ua tr ks /\ loop_inv_s c los his la ua tr ks m all i uniq unf /\
                    i < Seq.length all /\ index_s c los his la ua tr (Seq.index all i) < Seq.length m)
          (ensures (let p = index_s c los his la ua tr (Seq.index all i) in
                    (p >= 0 /\ not (Seq.index m p) ==> loop_inv_s c los his la ua tr ks (Seq.upd m p true) all (i + 1) (uniq + 1) unf) /\
                    (p >= 0 /\ Seq.index m p ==> loop_inv_s c los his la ua tr ks m all (i + 1) uniq unf) /\
                    (p < 0 ==> loop_inv_s c los his la ua tr ks m all (i + 1) uniq (unf + 1))))
  = loop_step_g c (ok_s c los his la ua) tr ks m all i uniq unf

let loop_done_s (#a #b: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
                (m: Seq.seq bool) (all: Seq.seq a) (i: int) (uniq unf: int)
  : Lemma (requires loop_inv_s c los his la ua tr ks m all i uniq unf /\ (i == Seq.length all \/ unf > 0))
          (ensures (unf > 0) == (unfound_s c los his la ua ks all > 0) /\
                   (i == Seq.length all ==> uniq == found_s c los his la ua ks all /\ unf == unfound_s c los his la ua ks all))
  = unfound_mono c (ok_s c los his la ua) ks all i;
    if i = Seq.length all then Seq.lemma_eq_intro (Seq.slice all 0 i) all

let loop_end_s (#a #b: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (tr: T.tree (a & b)) (ks: Seq.seq a)
               (m: Seq.seq bool) (all: Seq.seq a) (uniq unf: int) (stopped: bool)
  : Lemma (requires (stopped ==> unf > 0 /\ unfound_s c los his la ua ks all > 0) /\
                    (not stopped ==> loop_inv_s c los his la ua tr ks m all (Seq.length all) uniq unf))
          (ensures (unf > 0) == (unfound_s c los his la ua ks all > 0) /\
                   (not stopped ==> uniq == found_s c los his la ua ks all /\ unf == unfound_s c los his la ua ks all))
  = if not stopped then loop_done_s c los his la ua tr ks m all (Seq.length all) uniq unf

/// The early exit: no key, or none within the view's range.
let empty_counts_s (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (ks s: Seq.seq a)
  : Lemma (requires S.strictly_sorted c ks /\
                    (Seq.length ks == 0 \/
                     (has_bound los his la ua /\ Seq.length (RW.filter c (pk los his) (pk his los) la ua ks) == 0)))
          (ensures unfound_s c los his la ua ks s == Seq.length s /\ found_s c los his la ua ks s == 0)
  = if Seq.length ks = 0 then unfound_no_keys c (ok_s c los his la ua) ks s
    else empty_range_counts c (pk los his) (pk his los) la ua ks s

/// The counts the contracts state: the set's with no bound, the view's range's with one each.
let counts_s (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool) (ks s: Seq.seq a)
  : Lemma (ensures (not la /\ not ua ==> found_s c los his la ua ks s == found_all c ks s /\
                                         unfound_s c los his la ua ks s == unfound_all c ks s) /\
                   (forall (lo hi: a). {:pattern (found_range c lo hi la ua ks s) \/ (unfound_range c lo hi la ua ks s)}
                      los == one lo /\ his == one hi ==>
                      found_s c los his la ua ks s == found_range c lo hi la ua ks s /\
                      unfound_s c los his la ua ks s == unfound_range c lo hi la ua ks s))
  = let aux (lo hi: a)
      : Lemma (los == one lo /\ his == one hi ==>
               found_s c los his la ua ks s == found_range c lo hi la ua ks s /\
               unfound_s c los his la ua ks s == unfound_range c lo hi la ua ks s)
      = if not (la || ua) then counts_off c lo hi ks s in
    FStar.Classical.forall_intro_2 aux
