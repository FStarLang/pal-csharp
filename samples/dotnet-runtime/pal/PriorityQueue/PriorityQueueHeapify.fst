module PriorityQueueHeapify

/// `PriorityQueue.Heapify`'s proof (pal-csharp doc/translation.md R34.18), on top of
/// `Pulse.Lib.CSharp.Heap`. `MoveDown*` sifts a node down from a root `r` and only ever
/// writes inside `r`'s subtree; its loop invariant `down_r` is `Heap.down_inv` relative to
/// that subtree, so it serves both a whole heap with a hole at `r` (`Remove`, `Dequeue`)
/// and bottom-up construction, where only the subtrees below `r` are heaps (`Heapify`).
/// Every definition here is a definition; nothing is assumed.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module SD = Pulse.Lib.CSharp.Sorted
module S = Pulse.Lib.CSharp.Sort
module H = Pulse.Lib.CSharp.Heap

let pi_lt (j: int) : Lemma (requires 0 < j) (ensures 0 <= H.pi j /\ H.pi j < j) = ()

/// Node `j` is in the subtree rooted at `r` of the 4-ary heap.
let rec in_sub (r j: int) : Tot bool (decreases (if j < 0 then 0 else j)) =
  if j = r then true
  else if j > r && j > 0 then (pi_lt j; in_sub r (H.pi j))
  else false

let in_sub_ge (r j: int) : Lemma (requires in_sub r j) (ensures r <= j) = ()

/// A child of a node of the subtree is in it.
let in_sub_child (r j: int)
  : Lemma (requires 0 < j /\ in_sub r (H.pi j)) (ensures in_sub r j)
  = in_sub_ge r (H.pi j)

/// The subtree's root is not below itself.
let not_in_sub_parent (r: int)
  : Lemma (requires 0 < r) (ensures ~ (in_sub r (H.pi r)))
  = if in_sub r (H.pi r) then in_sub_ge r (H.pi r)

(* ------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* ------------------------------------------------------------------------- *)

/// The edges of `s[0, n)` inside `r`'s subtree that do not touch the hole `h` are in order.
let sub_heap_except (#e #p: Type) (c: O.comparer p) (s: Seq.seq (e & p)) (n r h: int) : prop =
  forall (j: nat).
    0 < j /\ j < n /\ n <= Seq.length s /\ in_sub r (H.pi j) /\ j <> h /\ H.pi j <> h ==>
    H.le c (Seq.index s (H.pi j)) (Seq.index s j)

/// `PQSpec.SubHeap(s, n, r, c)`: the subtree of `s[0, n)` rooted at `r` is a heap.
let sub_heap (#e #p: Type) (c: O.comparer p) (s: Seq.seq (e & p)) (n r: int) : prop =
  forall (j: nat).
    0 < j /\ j < n /\ n <= Seq.length s /\ in_sub r (H.pi j) ==>
    H.le c (Seq.index s (H.pi j)) (Seq.index s j)

/// `PQSpec.HeapAbove(s, n, lo, c)`: every edge of `s[0, n)` whose parent is above `lo` is in
/// order: every subtree rooted beyond `lo` is a heap. `HeapAbove(s, n, -1, c)` is a heap.
let heap_above (#e #p: Type) (c: O.comparer p) (s: Seq.seq (e & p)) (n lo: int) : prop =
  n <= Seq.length s /\
  (forall (j: nat). 0 < j /\ j < n /\ H.pi j > lo ==>
     H.le c (Seq.index s (H.pi j)) (Seq.index s j))

/// `PQSpec.DownR(s0, n, r, h, x, c, t, s)`: `MoveDown`'s loop, started at `r` on `s0`. `x` is
/// on its way down to the hole `h`; the subtree with `x` in the hole is a heap but for the
/// hole's edges; outside the subtree `s` is `s0`; and `r` holds what a caller may rely on: `x`
/// itself while the hole is there, a child of `r` in `s0` once it moved down.
[@@"opaque_to_smt"]
let down_r_core (#e #p: Type) (s0: Seq.seq (e & p)) (n r h: int) (x: e & p) (c: O.comparer p)
  (t s: Seq.seq (e & p)) : prop =
  0 <= r /\ r <= h /\ h < n /\ n <= Seq.length s /\ Seq.length s0 == Seq.length s /\
  in_sub r h /\
  sub_heap_except c s n r h /\
  (h <> r ==> H.le c (Seq.index s (H.pi h)) x) /\
  (h <> r ==> H.below c s n h (Seq.index s (H.pi h))) /\
  S.permutation t (Seq.upd (Seq.slice s 0 n) h x) /\
  (forall (j: nat). j < Seq.length s /\ ~ (in_sub r j) ==> Seq.index s j == Seq.index s0 j) /\
  (h == r ==> s == s0) /\
  (h <> r ==> (exists (k: nat). 0 < k /\ k < n /\ H.pi k == r /\ Seq.index s r == Seq.index s0 k))

let down_r (#e #p: Type) (s0: Seq.seq (e & p)) (n r h: int) (x: e & p) (c: O.comparer p)
  (t s: Seq.seq (e & p)) : prop =
  0 <= r /\ r <= h /\ h < n /\ n <= Seq.length s /\ down_r_core s0 n r h x c t s

(* ------------------------------------------------------------------------- *)
(* MoveDown                                                                   *)
(* ------------------------------------------------------------------------- *)

/// The start, from either precondition: a whole heap with a hole at `r`, or every subtree
/// below `r` a heap.
let down_r_init (e p: Type) (s: Seq.seq (e & p)) (n r: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p))
  : Lemma (requires 0 <= r /\ r < n /\ n <= Seq.length s /\ t == Seq.upd (Seq.slice s 0 n) r x /\
                    (H.down_inv e p s n r x c t \/ heap_above c s n r))
          (ensures down_r s n r r x c t s)
  = reveal_opaque (`%down_r_core) (down_r_core #e #p);
    reveal_opaque (`%H.down_core) (H.down_core e p);
    S.permutation_refl t;
    introduce forall (j: nat).
        0 < j /\ j < n /\ n <= Seq.length s /\ in_sub r (H.pi j) /\ j <> r /\ H.pi j <> r ==>
        H.le c (Seq.index s (H.pi j)) (Seq.index s j)
    with introduce _ ==> _ with begin
      in_sub_ge r (H.pi j);
      if H.down_inv e p s n r x c t then () else ()
    end

let down_r_step (e p: Type) (s0 s: Seq.seq (e & p)) (n r h: int) (x: e & p) (m: int)
  (c: O.comparer p) (t: Seq.seq (e & p))
  : Lemma (requires down_r s0 n r h x c t s /\ 4 * h + 1 < n /\
                    H.min_child e p s (4 * h + 1) (if 4 * h + 5 < n then 4 * h + 5 else n) m c /\
                    O.compare (SD.or_default c) (snd x) (snd (Seq.index s m)) > 0)
          (ensures down_r s0 n r m x c t (Seq.upd s h (Seq.index s m)))
  = reveal_opaque (`%down_r_core) (down_r_core #e #p);
    let y = Seq.index s m in
    let s' = Seq.upd s h y in
    let hi = if 4 * h + 5 < n then 4 * h + 5 else n in
    assert (4 * h + 1 <= m /\ m < hi /\ h < m /\ r < m);
    H.pi_child h m;
    assert (H.pi m == h);
    in_sub_child r m;
    let child (i: nat) : Lemma (requires 0 < i /\ i < n /\ H.pi i == h) (ensures 4 * h + 1 <= i /\ i < hi) =
      H.pi_child h i in
    introduce forall (j: nat).
        0 < j /\ j < n /\ n <= Seq.length s' /\ in_sub r (H.pi j) /\ j <> m /\ H.pi j <> m ==>
        H.le c (Seq.index s' (H.pi j)) (Seq.index s' j)
    with introduce _ ==> _ with begin
      if j = h then begin
        if h = r then not_in_sub_parent r;
        assert (h <> r);
        assert (H.le c (Seq.index s (H.pi h)) y)
      end
      else if H.pi j = h then child j
      else assert (H.le c (Seq.index s (H.pi j)) (Seq.index s j))
    end;
    assert (H.le c y x);
    introduce forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s' /\ H.pi i == m ==>
                               H.le c y (Seq.index s' i)
    with introduce _ ==> _ with begin
      H.grandchild h m i;
      in_sub_child r i;
      assert (H.le c (Seq.index s (H.pi i)) (Seq.index s i))
    end;
    let u = Seq.upd (Seq.slice s 0 n) h x in
    S.permutation_swap t u h m;
    H.swap_hole s n h m x;
    introduce forall (j: nat). j < Seq.length s' /\ ~ (in_sub r j) ==> Seq.index s' j == Seq.index s0 j
    with introduce _ ==> _ with ();
    assert (S.permutation t (Seq.upd (Seq.slice s' 0 n) m x));
    assert (H.below c s' n m y);
    assert (H.le c (Seq.index s' (H.pi m)) x);
    assert (in_sub r m /\ m <> r);
    let witness () : Lemma (exists (k: nat). 0 < k /\ k < n /\ H.pi k == r /\ Seq.index s' r == Seq.index s0 k)
      = if h = r then assert (0 < m /\ m < n /\ H.pi m == r /\ Seq.index s' r == Seq.index s0 m)
        else assert (Seq.index s' r == Seq.index s r) in
    witness ()

let down_r_done (e p: Type) (s0 s: Seq.seq (e & p)) (n r h: int) (x: e & p) (m: int)
  (c: O.comparer p) (t: Seq.seq (e & p))
  : Lemma (requires down_r s0 n r h x c t s /\ H.down_stop e p s n h x m c)
          (ensures sub_heap c (Seq.upd s h x) n r /\
                   S.permutation t (Seq.slice (Seq.upd s h x) 0 n))
  = reveal_opaque (`%down_r_core) (down_r_core #e #p);
    let s' = Seq.upd s h x in
    let rr = SD.or_default c in
    let hi = if 4 * h + 5 < n then 4 * h + 5 else n in
    introduce forall (j: nat).
        0 < j /\ j < n /\ n <= Seq.length s' /\ in_sub r (H.pi j) ==>
        H.le c (Seq.index s' (H.pi j)) (Seq.index s' j)
    with introduce _ ==> _ with begin
      if j = h then begin
        if h = r then not_in_sub_parent r
      end
      else if H.pi j = h then begin
        H.pi_child h j;
        assert (4 * h + 1 <= j /\ j < hi);
        O.compare_trans rr (snd x) (snd (Seq.index s m)) (snd (Seq.index s j))
      end
      else assert (H.le c (Seq.index s (H.pi j)) (Seq.index s j))
    end;
    Seq.lemma_eq_intro (Seq.slice s' 0 n) (Seq.upd (Seq.slice s 0 n) h x)

/// The exit: either the guard failed -- the hole has no child -- or the loop broke having
/// already established the result.
let down_r_finish (e p: Type) (s0 s: Seq.seq (e & p)) (n r h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p)) (i: int)
  : Lemma (requires down_r s0 n r h x c t s /\
                    ((i == 4 * h + 1 /\ i >= n) \/
                     (sub_heap c (Seq.upd s h x) n r /\
                      S.permutation t (Seq.slice (Seq.upd s h x) 0 n))))
          (ensures sub_heap c (Seq.upd s h x) n r /\
                   S.permutation t (Seq.slice (Seq.upd s h x) 0 n))
  = if 4 * h + 1 >= n then down_r_done e p s0 s n r h x 0 c t

/// What the caller gets: with a whole heap but for the hole at `r` before, a heap; with
/// every subtree below `r` a heap before, every subtree from `r` on.
let down_r_result (e p: Type) (s0 s: Seq.seq (e & p)) (n r h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p))
  : Lemma (requires down_r s0 n r h x c t s /\ sub_heap c (Seq.upd s h x) n r)
          (ensures (H.down_inv e p s0 n r x c t ==> H.is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c) /\
                   (heap_above c s0 n r ==> heap_above c (Seq.upd s h x) n (r - 1)))
  = reveal_opaque (`%down_r_core) (down_r_core #e #p);
    let s' = Seq.upd s h x in
    let outside (j: nat)
      : Lemma (requires j < Seq.length s /\ ~ (in_sub r j)) (ensures Seq.index s' j == Seq.index s0 j)
      = () in
    let not_sub (j: nat)
      : Lemma (requires 0 < j /\ j <> r /\ ~ (in_sub r (H.pi j))) (ensures ~ (in_sub r j))
      = () in
    introduce H.down_inv e p s0 n r x c t ==> H.is_heap e p (Seq.slice s' 0 n) c
    with begin
      reveal_opaque (`%H.down_core) (H.down_core e p);
      let u = Seq.slice s' 0 n in
      introduce forall (j: nat). 0 < j /\ j < n ==> H.le c (Seq.index u (H.pi j)) (Seq.index u j)
      with introduce _ ==> _ with begin
        if in_sub r (H.pi j) then ()
        else if j = r then begin
          outside (H.pi r);
          if h = r then ()
          else begin
            eliminate exists (k: nat). 0 < k /\ k < n /\ H.pi k == r /\ Seq.index s r == Seq.index s0 k
            with (assert (H.le c (Seq.index s0 (H.pi r)) (Seq.index s0 k)))
          end
        end
        else begin
          not_sub j;
          outside j;
          outside (H.pi j);
          assert (H.le c (Seq.index s0 (H.pi j)) (Seq.index s0 j))
        end
      end
    end;
    introduce heap_above c s0 n r ==> heap_above c s' n (r - 1)
    with begin
      introduce forall (j: nat). 0 < j /\ j < n /\ H.pi j > r - 1 ==>
                                 H.le c (Seq.index s' (H.pi j)) (Seq.index s' j)
      with introduce _ ==> _ with begin
        if in_sub r (H.pi j) then ()
        else begin
          pi_lt j;
          assert (H.pi j > r /\ j <> r /\ j < Seq.length s);
          not_sub j;
          outside j;
          outside (H.pi j);
          assert (H.le c (Seq.index s0 (H.pi j)) (Seq.index s0 j))
        end
      end
    end

(* ------------------------------------------------------------------------- *)
(* Heapify                                                                    *)
(* ------------------------------------------------------------------------- *)

/// The start: no edge of `s[0, n)` has a parent beyond the last parent.
let heap_above_init (e p: Type) (s: Seq.seq (e & p)) (n: int) (c: O.comparer p)
  : Lemma (requires 1 < n /\ n <= Seq.length s) (ensures heap_above c s n ((n - 2) / 4))
  = introduce forall (j: nat). 0 < j /\ j < n /\ H.pi j > (n - 2) / 4 ==>
                               H.le c (Seq.index s (H.pi j)) (Seq.index s j)
    with introduce _ ==> _ with FStar.Math.Lemmas.lemma_div_le (j - 1) (n - 2) 4

/// The end: every subtree from the root on is a heap.
let heap_above_done (e p: Type) (s: Seq.seq (e & p)) (n: int) (c: O.comparer p)
  : Lemma (requires heap_above c s n (-1) /\ 0 <= n)
          (ensures H.is_heap e p (Seq.slice s 0 n) c)
  = let u = Seq.slice s 0 n in
    introduce forall (j: nat). 0 < j /\ j < n ==> H.le c (Seq.index u (H.pi j)) (Seq.index u j)
    with introduce _ ==> _ with pi_lt j

/// `MoveDown(nodes[i], i)` starts from the heap-to-be the nodes already are.
let set_at_same (e p: Type) (s: Seq.seq (e & p)) (n i: int)
  : Lemma (requires 0 <= i /\ i < n /\ n <= Seq.length s)
          (ensures Seq.upd (Seq.slice s 0 n) i (Seq.index s i) == Seq.slice s 0 n)
  = Seq.lemma_eq_intro (Seq.upd (Seq.slice s 0 n) i (Seq.index s i)) (Seq.slice s 0 n)

/// A permutation of a permutation, for every intermediate sequence at once.
let permutation_trans_all (#t: Type) (a d: Seq.seq t)
  : Lemma (forall (b: Seq.seq t). S.permutation a b /\ S.permutation b d ==> S.permutation a d)
  = introduce forall (b: Seq.seq t). S.permutation a b /\ S.permutation b d ==> S.permutation a d
    with introduce _ ==> _ with H.permutation_trans a b d

(* ------------------------------------------------------------------------- *)
(* EnqueueRange                                                               *)
(* ------------------------------------------------------------------------- *)

/// One `Enqueue` of the `k`-th item of `c` extends the permutation of `a ++ c[0, k-1)`.
let enqueue_step (#t: Type) (a c b b': Seq.seq t) (k: int)
  : Lemma (requires 0 < k /\ k <= Seq.length c /\
                    S.permutation (Seq.append a (Seq.slice c 0 (k - 1))) b /\
                    S.permutation (Seq.snoc b (Seq.index c (k - 1))) b')
          (ensures S.permutation (Seq.append a (Seq.slice c 0 k)) b')
  = let x = Seq.index c (k - 1) in
    H.permutation_snoc (Seq.append a (Seq.slice c 0 (k - 1))) b x;
    Seq.lemma_eq_intro (Seq.snoc (Seq.append a (Seq.slice c 0 (k - 1))) x) (Seq.append a (Seq.slice c 0 k));
    H.permutation_trans (Seq.append a (Seq.slice c 0 k)) (Seq.snoc b x) b'

/// The heapified items of an empty queue are a permutation of the old items and the new.
let append_empty (#t: Type) (a c: Seq.seq t)
  : Lemma (requires Seq.length a == 0) (ensures Seq.append a c == c)
  = Seq.lemma_eq_intro (Seq.append a c) c

/// Nothing enqueued yet.
let append_nothing (#t: Type) (a c: Seq.seq t)
  : Lemma (Seq.append a (Seq.slice c 0 0) == a)
  = Seq.lemma_eq_intro (Seq.append a (Seq.slice c 0 0)) a

/// One more item copied: the filled prefix grows by the item at `i`.
let fill_step (#t: Type) (s c: Seq.seq t) (i: int) (x: t)
  : Lemma (requires 0 <= i /\ i < Seq.length s /\ i < Seq.length c /\
                    Seq.slice s 0 i == Seq.slice c 0 i /\ x == Seq.index c i)
          (ensures Seq.slice (Seq.upd s i x) 0 (i + 1) == Seq.slice c 0 (i + 1))
  = assert (forall (j: nat). j < i ==> Seq.index (Seq.slice s 0 i) j == Seq.index (Seq.slice c 0 i) j);
    Seq.lemma_eq_intro (Seq.slice (Seq.upd s i x) 0 (i + 1)) (Seq.slice c 0 (i + 1))
