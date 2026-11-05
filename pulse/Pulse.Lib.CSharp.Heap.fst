module Pulse.Lib.CSharp.Heap

/// The array-backed quaternary min-heap of `PriorityQueue<TElement, TPriority>`
/// (doc/translation.md R26.10): the heap property, the minimum it puts at the root, and
/// the invariants of the two hole-moving loops (`MoveUp*`, `MoveDown*`) with the lemmas
/// that carry each across an iteration. Verified, no admits; the only trusted facts are
/// the comparer axioms of `Order` (R22.30).
///
/// A node is a pair `(element, priority)`; only the priority is compared, at the order the
/// queue's comparer resolves to (`null` is `Comparer<TPriority>.Default`). The functions
/// C# names take their type arguments explicitly (R14.5).

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module SD = Pulse.Lib.CSharp.Sorted
module S = Pulse.Lib.CSharp.Sort

(* ------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* ------------------------------------------------------------------------- *)

/// The parent of node `i > 0`: `(i - 1) >> 2`.
let pi (i: int) : int = (i - 1) / 4

/// `x`'s priority is at most `y`'s.
let le (#e #p: Type) (c: O.comparer p) (x y: e & p) : prop =
  O.compare (SD.or_default c) (snd x) (snd y) <= 0

/// `PQSpec.IsHeap(s, comparer)`: every node's priority is at least its parent's.
let is_heap (e p: Type) (s: Seq.seq (e & p)) (c: O.comparer p) : prop =
  forall (i: nat).
    0 < i /\ i < Seq.length s ==> le c (Seq.index s (pi i)) (Seq.index s i)

/// `PQSpec.IsMin(s, x, comparer)`: no node's priority is below `x`'s.
let is_min (e p: Type) (s: Seq.seq (e & p)) (x: e & p) (c: O.comparer p) : prop =
  forall (k: nat). k < Seq.length s ==> le c x (Seq.index s k)

/// The edges of `s[0, n)` that do not touch the hole `h` are in order.
let heap_except (#e #p: Type) (c: O.comparer p) (s: Seq.seq (e & p)) (n h: int) : prop =
  forall (i: nat).
    0 < i /\ i < n /\ n <= Seq.length s /\ i <> h /\ pi i <> h ==>
    le c (Seq.index s (pi i)) (Seq.index s i)

/// Every child of `h` in `s[0, n)` has priority at least `y`'s.
let below (#e #p: Type) (c: O.comparer p) (s: Seq.seq (e & p)) (n h: int) (y: e & p) : prop =
  forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s /\ pi i == h ==> le c y (Seq.index s i)

/// `PQSpec.UpInv(s, n, h, x, comparer, t)`: `MoveUp`'s loop. `x` is on its way up to the
/// hole `h`; the heap with `x` in the hole is `t` reordered.
[@@"opaque_to_smt"]
let up_core (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p)) : prop =
  0 <= h /\ h < n /\ n <= Seq.length s /\
  heap_except c s n h /\
  below c s n h x /\
  (h > 0 ==> below c s n h (Seq.index s (pi h))) /\
  S.permutation t (Seq.upd (Seq.slice s 0 n) h x)

let up_inv (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p)) : prop =
  0 <= h /\ h < n /\ n <= Seq.length s /\ up_core e p s n h x c t

/// `PQSpec.UpStop(s, h, x, comparer)`: `x` may stay in the hole `h`.
let up_stop (e p: Type) (s: Seq.seq (e & p)) (h: int) (x: e & p) (c: O.comparer p) : prop =
  h <= 0 \/ (h < Seq.length s /\ O.compare (SD.or_default c) (snd x) (snd (Seq.index s (pi h))) >= 0)

/// `PQSpec.DownInv(s, n, h, x, comparer, t)`: `MoveDown`'s loop. `x` is on its way down
/// to the hole `h`; the heap with `x` in the hole is `t` reordered.
[@@"opaque_to_smt"]
let down_core (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p)) : prop =
  0 <= h /\ h < n /\ n <= Seq.length s /\
  heap_except c s n h /\
  (h > 0 ==> le c (Seq.index s (pi h)) x) /\
  (h > 0 ==> below c s n h (Seq.index s (pi h))) /\
  S.permutation t (Seq.upd (Seq.slice s 0 n) h x)

let down_inv (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p)) : prop =
  0 <= h /\ h < n /\ n <= Seq.length s /\ down_core e p s n h x c t

/// `PQSpec.MinChild(s, first, i, m, comparer)`: `s[m]` is a least of `s[first, i)`.
let min_child (e p: Type) (s: Seq.seq (e & p)) (first i m: int) (c: O.comparer p) : prop =
  0 <= first /\ first <= m /\ m < i /\ i <= Seq.length s /\
  (forall (k: nat). first <= k /\ k < i ==> le c (Seq.index s m) (Seq.index s k))

/// `PQSpec.DownStop(s, n, h, x, m, comparer)`: `x` may stay in the hole `h`: it has no
/// child, or `s[m]`, a least of its children, is not below it.
let down_stop (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (m: int) (c: O.comparer p) : prop =
  0 <= h /\ (4 * h + 1 >= n \/
   (min_child e p s (4 * h + 1) (if 4 * h + 5 < n then 4 * h + 5 else n) m c /\
    O.compare (SD.or_default c) (snd x) (snd (Seq.index s m)) <= 0))

(* ------------------------------------------------------------------------- *)
(* Permutations                                                               *)
(* ------------------------------------------------------------------------- *)

let permutation_intro (#t: Type) (a b: Seq.seq t) (f: nat -> nat)
  : Lemma (requires Seq.length a == Seq.length b /\ S.is_bij (Seq.length a) f /\
                    (forall (i: nat). i < Seq.length a ==> Seq.index b i == Seq.index a (f i)))
          (ensures S.permutation a b)
  = reveal_opaque (`%S.permutation) (S.permutation #t)

let permutation_trans_with (#t: Type) (a b d: Seq.seq t) (f g: nat -> nat)
  : Lemma (requires Seq.length a == Seq.length b /\ Seq.length b == Seq.length d /\
                    S.is_bij (Seq.length a) f /\
                    (forall (i: nat). i < Seq.length a ==> Seq.index b i == Seq.index a (f i)) /\
                    S.is_bij (Seq.length b) g /\
                    (forall (i: nat). i < Seq.length b ==> Seq.index d i == Seq.index b (g i)))
          (ensures S.permutation a d)
  = let n = Seq.length a in
    let h (i: nat) : nat = f (g i) in
    let inj (i j: nat) : Lemma (i < n /\ j < n /\ h i == h j ==> i == j) =
      if i < n && j < n then (assert (g i < n /\ g j < n)) in
    Classical.forall_intro_2 inj;
    let pt (i: nat) : Lemma (i < n ==> Seq.index d i == Seq.index a (h i)) =
      if i < n then (assert (g i < n); assert (Seq.index b (g i) == Seq.index a (f (g i)))) in
    Classical.forall_intro pt;
    assert (S.is_bij n h);
    permutation_intro a d h

let permutation_trans (#t: Type) (a b d: Seq.seq t)
  : Lemma (requires S.permutation a b /\ S.permutation b d) (ensures S.permutation a d)
  = reveal_opaque (`%S.permutation) (S.permutation #t);
    eliminate exists (f: nat -> nat). S.is_bij (Seq.length a) f /\
        (forall (i: nat). i < Seq.length a ==> Seq.index b i == Seq.index a (f i))
    with eliminate exists (g: nat -> nat). S.is_bij (Seq.length b) g /\
        (forall (i: nat). i < Seq.length b ==> Seq.index d i == Seq.index b (g i))
    with permutation_trans_with a b d f g

let permutation_snoc_with (#t: Type) (a b: Seq.seq t) (x: t) (f: nat -> nat)
  : Lemma (requires Seq.length a == Seq.length b /\ S.is_bij (Seq.length a) f /\
                    (forall (i: nat). i < Seq.length a ==> Seq.index b i == Seq.index a (f i)))
          (ensures S.permutation (Seq.snoc a x) (Seq.snoc b x))
  = let n = Seq.length a in
    let g (i: nat) : nat = if i < n then f i else i in
    let inj (i j: nat) : Lemma (i < n + 1 /\ j < n + 1 /\ g i == g j ==> i == j) = () in
    Classical.forall_intro_2 inj;
    let pt (i: nat) : Lemma (i < n + 1 ==> Seq.index (Seq.snoc b x) i == Seq.index (Seq.snoc a x) (g i)) =
      if i < n then (assert (Seq.index (Seq.snoc b x) i == Seq.index b i);
                     assert (Seq.index (Seq.snoc a x) (f i) == Seq.index a (f i))) in
    Classical.forall_intro pt;
    permutation_intro (Seq.snoc a x) (Seq.snoc b x) g

let permutation_snoc (#t: Type) (a b: Seq.seq t) (x: t)
  : Lemma (requires S.permutation a b) (ensures S.permutation (Seq.snoc a x) (Seq.snoc b x))
  = reveal_opaque (`%S.permutation) (S.permutation #t);
    eliminate exists (f: nat -> nat). S.is_bij (Seq.length a) f /\
        (forall (i: nat). i < Seq.length a ==> Seq.index b i == Seq.index a (f i))
    with permutation_snoc_with a b x f

let heap_edge (#e #p: Type) (c: O.comparer p) (s: Seq.seq (e & p)) (i: nat)
  : Lemma (requires is_heap e p s c /\ 0 < i /\ i < Seq.length s)
          (ensures le c (Seq.index s (pi i)) (Seq.index s i))
  = ()

(* ------------------------------------------------------------------------- *)
(* The minimum                                                                *)
(* ------------------------------------------------------------------------- *)

let rec root_le (#e #p: Type) (c: O.comparer p) (s: Seq.seq (e & p)) (k: nat)
  : Lemma (requires is_heap e p s c /\ k < Seq.length s)
          (ensures le c (Seq.index s 0) (Seq.index s k))
          (decreases k)
  = if k = 0 then ()
    else begin
      root_le c s (pi k);
      O.compare_trans (SD.or_default c) (snd (Seq.index s 0)) (snd (Seq.index s (pi k))) (snd (Seq.index s k))
    end

/// The root of a heap is a minimum.
let heap_min (e p: Type) (s: Seq.seq (e & p)) (c: O.comparer p)
  : Lemma (requires is_heap e p s c /\ Seq.length s > 0)
          (ensures is_min e p s (Seq.index s 0) c)
          [SMTPat (is_min e p s (Seq.index s 0) c)]
  = introduce forall (k: nat). k < Seq.length s ==> le c (Seq.index s 0) (Seq.index s k)
    with introduce _ ==> _ with root_le c s k

/// A prefix of a heap is a heap.
let heap_prefix (e p: Type) (s: Seq.seq (e & p)) (c: O.comparer p) (m: nat)
  : Lemma (requires is_heap e p s c /\ m <= Seq.length s)
          (ensures is_heap e p (Seq.slice s 0 m) c)
          [SMTPat (is_heap e p (Seq.slice s 0 m) c)]
  = let s' = Seq.slice s 0 m in
    introduce forall (i: nat). 0 < i /\ i < m ==> le c (Seq.index s' (pi i)) (Seq.index s' i)
    with introduce _ ==> _ with heap_edge c s i

/// Up to `n`, only `s[0, n)` matters.
let is_heap_slice (e p: Type) (s0 s1: Seq.seq (e & p)) (c: O.comparer p) (n: nat)
  : Lemma (requires n <= Seq.length s0 /\ n <= Seq.length s1 /\
                    (forall (k: nat). k < n ==> Seq.index s0 k == Seq.index s1 k))
          (ensures is_heap e p (Seq.slice s0 0 n) c <==> is_heap e p (Seq.slice s1 0 n) c)
  = assert (Seq.slice s0 0 n `Seq.equal` Seq.slice s1 0 n)

/// Moving the hole from `h` to `q` exchanges two nodes of the heap with `x` in the hole.
let swap_hole (#t: Type) (s: Seq.seq t) (n h q: nat) (x: t)
  : Lemma (requires h < n /\ q < n /\ n <= Seq.length s /\ h <> q)
          (ensures S.swap (Seq.upd (Seq.slice s 0 n) h x) h q ==
                   Seq.upd (Seq.slice (Seq.upd s h (Seq.index s q)) 0 n) q x)
  = Seq.lemma_eq_intro (S.swap (Seq.upd (Seq.slice s 0 n) h x) h q)
                       (Seq.upd (Seq.slice (Seq.upd s h (Seq.index s q)) 0 n) q x)

(* ------------------------------------------------------------------------- *)
(* Moving a node up                                                           *)
(* ------------------------------------------------------------------------- *)

let up_init (e p: Type) (s: Seq.seq (e & p)) (n: int) (x: e & p) (c: O.comparer p)
  : Lemma (requires 0 < n /\ n <= Seq.length s /\ is_heap e p (Seq.slice s 0 (n - 1)) c)
          (ensures up_inv e p s n (n - 1) x c (Seq.snoc (Seq.slice s 0 (n - 1)) x))
  = reveal_opaque (`%up_core) (up_core e p);
    let h = n - 1 in
    let s' = Seq.slice s 0 h in
    introduce forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s /\ i <> h /\ pi i <> h ==>
                               le c (Seq.index s (pi i)) (Seq.index s i)
    with introduce _ ==> _ with assert (le c (Seq.index s' (pi i)) (Seq.index s' i));
    let t = Seq.snoc s' x in
    Seq.lemma_eq_intro t (Seq.upd (Seq.slice s 0 n) h x);
    S.permutation_refl t

let up_step (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p))
  : Lemma (requires up_inv e p s n h x c t /\ h > 0 /\
                    O.compare (SD.or_default c) (snd x) (snd (Seq.index s (pi h))) < 0)
          (ensures up_inv e p (Seq.upd s h (Seq.index s (pi h))) n (pi h) x c t)
  = reveal_opaque (`%up_core) (up_core e p);
    let q = pi h in
    let y = Seq.index s q in
    let s' = Seq.upd s h y in
    let r = SD.or_default c in
    // The edges that do not touch the new hole `q`.
    introduce forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s' /\ i <> q /\ pi i <> q ==>
                               le c (Seq.index s' (pi i)) (Seq.index s' i)
    with introduce _ ==> _ with
      (if i = h then ()
       else if pi i = h then
         // A child of the old hole: below its grandparent `y`, which now sits above it.
         assert (le c y (Seq.index s i))
       else assert (le c (Seq.index s (pi i)) (Seq.index s i)));
    // `x` is below every child of `q`: `y` itself, and `y`'s siblings, which are above `y`.
    introduce forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s' /\ pi i == q ==>
                               le c x (Seq.index s' i)
    with introduce _ ==> _ with
      (if i = h then ()
       else begin
         assert (le c (Seq.index s (pi i)) (Seq.index s i));
         O.compare_trans r (snd x) (snd y) (snd (Seq.index s i))
       end);
    // The grandparent of the new hole's children.
    introduce q > 0 ==> below c s' n q (Seq.index s' (pi q))
    with begin
      let g = Seq.index s (pi q) in
      assert (Seq.index s' (pi q) == g);
      assert (le c g y);
      introduce forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s' /\ pi i == q ==>
                                 le c g (Seq.index s' i)
      with introduce _ ==> _ with
        (if i = h then ()
         else begin
           assert (le c (Seq.index s (pi i)) (Seq.index s i));
           O.compare_trans r (snd g) (snd y) (snd (Seq.index s i))
         end)
    end;
    // The heap with `x` in the hole is the old one with two nodes exchanged.
    let u = Seq.upd (Seq.slice s 0 n) h x in
    S.permutation_swap t u h q;
    swap_hole s n h q x

let up_done (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p))
  : Lemma (requires up_inv e p s n h x c t /\ up_stop e p s h x c)
          (ensures is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c /\
                   S.permutation t (Seq.slice (Seq.upd s h x) 0 n))
  = reveal_opaque (`%up_core) (up_core e p);
    let s' = Seq.upd s h x in
    let u = Seq.slice s' 0 n in
    introduce forall (i: nat). 0 < i /\ i < n ==> le c (Seq.index u (pi i)) (Seq.index u i)
    with introduce _ ==> _ with
      (if i = h then ()
       else if pi i = h then ()
       else assert (le c (Seq.index s (pi i)) (Seq.index s i)));
    Seq.lemma_eq_intro u (Seq.upd (Seq.slice s 0 n) h x)

(* ------------------------------------------------------------------------- *)
(* Moving a node down                                                         *)
(* ------------------------------------------------------------------------- *)

let down_init (e p: Type) (s: Seq.seq (e & p)) (n: int) (x: e & p) (c: O.comparer p)
  : Lemma (requires 0 < n /\ n <= Seq.length s /\ is_heap e p (Seq.slice s 0 n) c)
          (ensures down_inv e p s n 0 x c (Seq.upd (Seq.slice s 0 n) 0 x))
  = reveal_opaque (`%down_core) (down_core e p);
    let s' = Seq.slice s 0 n in
    introduce forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s /\ i <> 0 /\ pi i <> 0 ==>
                               le c (Seq.index s (pi i)) (Seq.index s i)
    with introduce _ ==> _ with assert (le c (Seq.index s' (pi i)) (Seq.index s' i));
    S.permutation_refl (Seq.upd s' 0 x)

let min_child_init (e p: Type) (s: Seq.seq (e & p)) (first: int) (c: O.comparer p)
  : Lemma (requires 0 <= first /\ first < Seq.length s)
          (ensures min_child e p s first (first + 1) first c)
  = ()

let min_child_step (e p: Type) (s: Seq.seq (e & p)) (first i m: int) (c: O.comparer p)
  : Lemma (requires min_child e p s first i m c /\ i < Seq.length s)
          (ensures (O.compare (SD.or_default c) (snd (Seq.index s i)) (snd (Seq.index s m)) < 0 ==>
                      min_child e p s first (i + 1) i c) /\
                   (~ (O.compare (SD.or_default c) (snd (Seq.index s i)) (snd (Seq.index s m)) < 0) ==>
                      min_child e p s first (i + 1) m c))
  = let r = SD.or_default c in
    introduce O.compare r (snd (Seq.index s i)) (snd (Seq.index s m)) < 0 ==>
              min_child e p s first (i + 1) i c
    with begin
      introduce forall (k: nat). first <= k /\ k < i + 1 ==> le c (Seq.index s i) (Seq.index s k)
      with introduce _ ==> _ with
        (if k = i then ()
         else O.compare_trans r (snd (Seq.index s i)) (snd (Seq.index s m)) (snd (Seq.index s k)))
    end

/// The children of `h` are exactly `[4h + 1, 4h + 5)`.
let pi_child (h i: int)
  : Lemma (requires 0 <= h /\ 0 < i) (ensures pi i == h <==> 4 * h + 1 <= i /\ i < 4 * h + 5)
  = FStar.Math.Lemmas.euclidean_division_definition (i - 1) 4;
    FStar.Math.Lemmas.modulo_range_lemma (i - 1) 4

let grandchild (h m i: int)
  : Lemma (requires 0 <= h /\ 4 * h + 1 <= m /\ 0 < i /\ pi i == m)
          (ensures i <> h /\ pi i <> h)
  = pi_child m i

let down_step (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (m: int) (c: O.comparer p)
  (t: Seq.seq (e & p))
  : Lemma (requires down_inv e p s n h x c t /\ 4 * h + 1 < n /\
                    min_child e p s (4 * h + 1) (if 4 * h + 5 < n then 4 * h + 5 else n) m c /\
                    O.compare (SD.or_default c) (snd x) (snd (Seq.index s m)) > 0)
          (ensures down_inv e p (Seq.upd s h (Seq.index s m)) n m x c t)
  = reveal_opaque (`%down_core) (down_core e p);
    let y = Seq.index s m in
    let s' = Seq.upd s h y in
    let r = SD.or_default c in
    let hi = if 4 * h + 5 < n then 4 * h + 5 else n in
    pi_child h m;
    assert (pi m == h);
    let child (i: nat) : Lemma (requires 0 < i /\ i < n /\ pi i == h) (ensures 4 * h + 1 <= i /\ i < hi) =
      pi_child h i in
    introduce forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s' /\ i <> m /\ pi i <> m ==>
                               le c (Seq.index s' (pi i)) (Seq.index s' i)
    with introduce _ ==> _ with
      (if i = h then ()
       else if pi i = h then child i
       else assert (le c (Seq.index s (pi i)) (Seq.index s i)));
    assert (le c y x);
    introduce forall (i: nat). 0 < i /\ i < n /\ n <= Seq.length s' /\ pi i == m ==>
                               le c y (Seq.index s' i)
    with introduce _ ==> _ with begin
      grandchild h m i;
      assert (le c (Seq.index s (pi i)) (Seq.index s i))
    end;
    let u = Seq.upd (Seq.slice s 0 n) h x in
    S.permutation_swap t u h m;
    assert (h <> m);
    swap_hole s n h m x

let down_done (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (m: int) (c: O.comparer p)
  (t: Seq.seq (e & p))
  : Lemma (requires down_inv e p s n h x c t /\ down_stop e p s n h x m c)
          (ensures is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c /\
                   S.permutation t (Seq.slice (Seq.upd s h x) 0 n))
  = reveal_opaque (`%down_core) (down_core e p);
    let s' = Seq.upd s h x in
    let u = Seq.slice s' 0 n in
    let r = SD.or_default c in
    let hi = if 4 * h + 5 < n then 4 * h + 5 else n in
    introduce forall (i: nat). 0 < i /\ i < n ==> le c (Seq.index u (pi i)) (Seq.index u i)
    with introduce _ ==> _ with
      (if i = h then ()
       else if pi i = h then begin
         pi_child h i;
         assert (4 * h + 1 <= i /\ i < hi);
         O.compare_trans r (snd x) (snd (Seq.index s m)) (snd (Seq.index s i))
       end
       else assert (le c (Seq.index s (pi i)) (Seq.index s i)));
    Seq.lemma_eq_intro u (Seq.upd (Seq.slice s 0 n) h x)

/// What `RemoveRootNode` leaves: the old heap is the new one with its root put back.
let remove_root (e p: Type) (s: Seq.seq (e & p)) (n: nat) (a: Seq.seq (e & p))
  : Lemma (requires n < Seq.length s /\
                    (n == 0 ==> Seq.length a == 0) /\
                    (n > 0 ==> S.permutation (Seq.upd (Seq.slice s 0 n) 0 (Seq.index s n)) a))
          (ensures S.permutation (Seq.slice s 0 (n + 1)) (Seq.snoc a (Seq.index s 0)))
  = let full = Seq.slice s 0 (n + 1) in
    if n = 0 then begin
      Seq.lemma_eq_intro full (Seq.snoc a (Seq.index s 0));
      S.permutation_refl full
    end else begin
      let u = Seq.upd (Seq.slice s 0 n) 0 (Seq.index s n) in
      S.permutation_refl full;
      S.permutation_swap full full 0 n;
      Seq.lemma_eq_intro (S.swap full 0 n) (Seq.snoc u (Seq.index s 0));
      permutation_snoc u a (Seq.index s 0);
      permutation_trans full (Seq.snoc u (Seq.index s 0)) (Seq.snoc a (Seq.index s 0))
    end

(* ------------------------------------------------------------------------- *)
(* The steps as a program takes them                                          *)
(* ------------------------------------------------------------------------- *)

/// A loop invariant names its heap-to-be `t` with `Old`, which a proof step cannot; so
/// each step below holds for every `t` at once, and the caller never names it.

/// `Enqueue`'s start: the new node `x` is in the hole at the end of `s[0, n)`, which is
/// the old heap with `x` added.
let up_init_at (e p: Type) (s: Seq.seq (e & p)) (n: int) (x: e & p) (c: O.comparer p)
  : Lemma (requires 0 < n /\ n <= Seq.length s /\ is_heap e p (Seq.slice s 0 (n - 1)) c)
          (ensures up_inv e p s n (n - 1) x c (Seq.upd (Seq.slice s 0 n) (n - 1) x) /\
                   Seq.snoc (Seq.slice s 0 (n - 1)) x == Seq.upd (Seq.slice s 0 n) (n - 1) x)
  = up_init e p s n x c;
    Seq.lemma_eq_intro (Seq.snoc (Seq.slice s 0 (n - 1)) x) (Seq.upd (Seq.slice s 0 n) (n - 1) x)

let up_step_all (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  : Lemma (requires h > 0 /\ h < Seq.length s /\
                    O.compare (SD.or_default c) (snd x) (snd (Seq.index s (pi h))) < 0)
          (ensures forall (t: Seq.seq (e & p)). up_inv e p s n h x c t ==>
                     up_inv e p (Seq.upd s h (Seq.index s (pi h))) n (pi h) x c t)
  = introduce forall (t: Seq.seq (e & p)). up_inv e p s n h x c t ==>
                up_inv e p (Seq.upd s h (Seq.index s (pi h))) n (pi h) x c t
    with introduce _ ==> _ with up_step e p s n h x c t

let up_done_all (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  : Lemma (requires up_stop e p s h x c)
          (ensures forall (t: Seq.seq (e & p)). up_inv e p s n h x c t ==>
                     is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c /\
                     S.permutation t (Seq.slice (Seq.upd s h x) 0 n))
  = introduce forall (t: Seq.seq (e & p)). up_inv e p s n h x c t ==>
                is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c /\
                S.permutation t (Seq.slice (Seq.upd s h x) 0 n)
    with introduce _ ==> _ with up_done e p s n h x c t

let down_step_all (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (m: int) (c: O.comparer p)
  : Lemma (requires 0 <= h /\ 4 * h + 1 < n /\
                    min_child e p s (4 * h + 1) (if 4 * h + 5 < n then 4 * h + 5 else n) m c /\
                    O.compare (SD.or_default c) (snd x) (snd (Seq.index s m)) > 0)
          (ensures forall (t: Seq.seq (e & p)). down_inv e p s n h x c t ==>
                     down_inv e p (Seq.upd s h (Seq.index s m)) n m x c t)
  = introduce forall (t: Seq.seq (e & p)). down_inv e p s n h x c t ==>
                down_inv e p (Seq.upd s h (Seq.index s m)) n m x c t
    with introduce _ ==> _ with down_step e p s n h x m c t

let down_done_all (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (m: int) (c: O.comparer p)
  : Lemma (requires down_stop e p s n h x m c)
          (ensures forall (t: Seq.seq (e & p)). down_inv e p s n h x c t ==>
                     is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c /\
                     S.permutation t (Seq.slice (Seq.upd s h x) 0 n))
  = introduce forall (t: Seq.seq (e & p)). down_inv e p s n h x c t ==>
                is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c /\
                S.permutation t (Seq.slice (Seq.upd s h x) 0 n)
    with introduce _ ==> _ with down_done e p s n h x m c t

/// `MoveDown`'s exit: either the guard failed — the hole has no child — or the loop broke
/// having already established the result.
let down_finish (e p: Type) (s: Seq.seq (e & p)) (n h: int) (x: e & p) (c: O.comparer p)
  (t: Seq.seq (e & p)) (i: int)
  : Lemma (requires down_inv e p s n h x c t /\
                    ((i == 4 * h + 1 /\ i >= n) \/
                     (is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c /\
                      S.permutation t (Seq.slice (Seq.upd s h x) 0 n))))
          (ensures is_heap e p (Seq.slice (Seq.upd s h x) 0 n) c /\
                   S.permutation t (Seq.slice (Seq.upd s h x) 0 n))
  = if 4 * h + 1 >= n then down_done e p s n h x 0 c t

/// `DequeueEnqueue`'s short path: a node no greater than the root may replace it.
let replace_root (e p: Type) (s: Seq.seq (e & p)) (n: int) (x: e & p) (c: O.comparer p)
  : Lemma (requires 0 < n /\ n <= Seq.length s /\ is_heap e p (Seq.slice s 0 n) c /\
                    O.compare (SD.or_default c) (snd x) (snd (Seq.index s 0)) <= 0)
          (ensures is_heap e p (Seq.slice (Seq.upd s 0 x) 0 n) c /\
                   S.permutation (Seq.upd (Seq.slice s 0 n) 0 x) (Seq.slice (Seq.upd s 0 x) 0 n))
  = let u = Seq.slice s 0 n in
    let v = Seq.slice (Seq.upd s 0 x) 0 n in
    Seq.lemma_eq_intro (Seq.upd u 0 x) v;
    S.permutation_refl v;
    introduce forall (i: nat). 0 < i /\ i < n ==> le c (Seq.index v (pi i)) (Seq.index v i)
    with introduce _ ==> _ with begin
      if pi i = 0 then begin
        root_le c u i;
        O.compare_trans (SD.or_default c) (snd x) (snd (Seq.index s 0)) (snd (Seq.index s i))
      end else assert (le c (Seq.index u (pi i)) (Seq.index u i))
    end
