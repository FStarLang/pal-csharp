module Pulse.Lib.CSharp.RegionRing

/// R31.4. A region whose nodes form *rings*: circular doubly-linked lists, each owned by one
/// object that every node of the ring points back to (`LinkedList<T>`). The owner holds the
/// region (R27.4); what its fields mean is a pure function of the heap.
///
/// * `walk nx h x n` is the `n` boxes reached from `x` by following `nx`.
/// * `ring_seq nx pv h s`: the boxes of `s` are in the heap, distinct, and each one's `nx` is
///   the next (the last's the first) and its `pv` the one before (the first's the last).
/// * `owned view h s o`: the boxes of the heap whose owner (the second half of their view) is
///   `o` are exactly the boxes of `s`.
/// * `items view h s` is the first half of each view, in order.
///
/// Every definition a `[RegionOp]` names takes the region class's view and links first
/// (R27.22); the view is a pair of the item and the owner, a nullable box. The lemmas are
/// called explicitly, as ghost statements. Nothing here is trusted beyond
/// `Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8).

open Pulse.Lib.CSharp.Region
module B = Pulse.Lib.Box
module Seq = FStar.Seq

(* ------------------------------------------------------------------------------------ *)
(* Sequences of boxes                                                                     *)
(* ------------------------------------------------------------------------------------ *)

let in_seq (#a: Type0) (s: Seq.seq (B.box a)) (x: B.box a) : prop =
  exists (i: nat). i < Seq.length s /\ Seq.index s i == x

let distinct (#a: Type0) (s: Seq.seq (B.box a)) : prop =
  forall (i j: nat). i < Seq.length s /\ j < Seq.length s /\ Seq.index s i == Seq.index s j ==> i == j

let all_mem (#a: Type0) (h: heap a) (s: Seq.seq (B.box a)) : prop =
  forall (i: nat). i < Seq.length s ==> mem h (Seq.index s i)

/// The position of a box in a sequence, or -1.
let rec pos (#a: Type0) (s: Seq.seq (B.box a)) (x: B.box a) : Tot int (decreases Seq.length s) =
  if Seq.length s = 0 then -1
  else if eq_box (Seq.index s 0) x then 0
  else (let k = pos (Seq.tail s) x in if k < 0 then -1 else k + 1)

let rec pos_spec (#a: Type0) (s: Seq.seq (B.box a)) (x: B.box a)
  : Lemma (ensures (let k = pos s x in
                    -1 <= k /\ k < Seq.length s /\
                    (k >= 0 <==> in_seq s x) /\
                    (k >= 0 ==> Seq.index s k == x) /\
                    (forall (i: nat). i < k ==> ~ (Seq.index s i == x))))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if eq_box (Seq.index s 0) x then ()
    else begin
      pos_spec (Seq.tail s) x;
      introduce forall (i: nat). i < Seq.length s /\ Seq.index s i == x ==> in_seq (Seq.tail s) x
      with introduce _ ==> _ with (if i = 0 then () else assert (Seq.index (Seq.tail s) (i - 1) == x));
      introduce forall (i: nat). i < Seq.length (Seq.tail s) /\ Seq.index (Seq.tail s) i == x ==> in_seq s x
      with introduce _ ==> _ with assert (Seq.index s (i + 1) == x);
      let k = pos (Seq.tail s) x in
      assert (pos s x == (if k < 0 then -1 else k + 1));
      assert (k >= 0 ==> Seq.index s (k + 1) == Seq.index (Seq.tail s) k);
      introduce forall (i: nat). i < pos s x ==> ~ (Seq.index s i == x)
      with introduce _ ==> _ with (if i = 0 then () else assert (Seq.index s i == Seq.index (Seq.tail s) (i - 1)))
    end

/// In a sequence without repetitions, a box's position is the one it is at.
let pos_index (#a: Type0) (s: Seq.seq (B.box a)) (i: nat)
  : Lemma (requires distinct s /\ i < Seq.length s)
          (ensures pos s (Seq.index s i) == i)
  = pos_spec s (Seq.index s i)

/// `s` with `x` inserted at `i` (unchanged when `i` is out of range).
let insert_at (#t: Type) (s: Seq.seq t) (i: int) (x: t) : Seq.seq t =
  if 0 <= i && i <= Seq.length s
  then Seq.append (Seq.slice s 0 i) (Seq.cons x (Seq.slice s i (Seq.length s)))
  else s

/// `s` without its element at `i` (unchanged when `i` is out of range).
let remove_at (#t: Type) (s: Seq.seq t) (i: int) : Seq.seq t =
  if 0 <= i && i < Seq.length s
  then Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))
  else s

let insert_at_spec (#t: Type) (s: Seq.seq t) (i: int) (x: t)
  : Lemma (requires 0 <= i /\ i <= Seq.length s)
          (ensures Seq.length (insert_at s i x) == Seq.length s + 1 /\
                   (forall (j: nat). j < Seq.length s + 1 ==>
                      Seq.index (insert_at s i x) j ==
                        (if j < i then Seq.index s j else if j = i then x else Seq.index s (j - 1))))
  = ()

let remove_at_spec (#t: Type) (s: Seq.seq t) (i: int)
  : Lemma (requires 0 <= i /\ i < Seq.length s)
          (ensures Seq.length (remove_at s i) == Seq.length s - 1 /\
                   (forall (j: nat). j < Seq.length s - 1 ==>
                      Seq.index (remove_at s i) j == (if j < i then Seq.index s j else Seq.index s (j + 1))))
  = ()

(* ------------------------------------------------------------------------------------ *)
(* Walks and rings                                                                        *)
(* ------------------------------------------------------------------------------------ *)

/// The `n` boxes reached from `x` along `nx`: a box the heap does not hold links to null.
let rec walk (#a: Type0) (nx: a -> B.box a) (h: heap a) (x: B.box a) (n: int)
  : Tot (Seq.seq (B.box a)) (decreases (if n < 0 then 0 else n))
  = if n <= 0 then Seq.empty else Seq.cons x (walk nx h (link_at nx h x) (n - 1))

let rec walk_length (#a: Type0) (nx: a -> B.box a) (h: heap a) (x: B.box a) (n: int)
  : Lemma (ensures Seq.length (walk nx h x n) == (if n < 0 then 0 else n))
          (decreases (if n < 0 then 0 else n))
          [SMTPat (Seq.length (walk nx h x n))]
  = if n <= 0 then () else walk_length nx h (link_at nx h x) (n - 1)

let linked (#a: Type0) (nx pv: a -> B.box a) (h: heap a) (s: Seq.seq (B.box a)) : prop =
  (forall (i: nat). i + 1 < Seq.length s ==>
     link_at nx h (Seq.index s i) == Seq.index s (i + 1) /\
     link_at pv h (Seq.index s (i + 1)) == Seq.index s i) /\
  (Seq.length s > 0 ==>
     link_at nx h (Seq.index s (Seq.length s - 1)) == Seq.index s 0 /\
     link_at pv h (Seq.index s 0) == Seq.index s (Seq.length s - 1))

let non_null (#a: Type0) (s: Seq.seq (B.box a)) : prop =
  forall (i: nat). i < Seq.length s ==> ~ (B.is_null (Seq.index s i))

let ring_seq (#a: Type0) (nx pv: a -> B.box a) (h: heap a) (s: Seq.seq (B.box a)) : prop =
  all_mem h s /\ distinct s /\ non_null s /\ linked nx pv h s

let rec walk_from (#a: Type0) (nx: a -> B.box a) (h: heap a) (s: Seq.seq (B.box a)) (i: nat)
  : Lemma (requires i < Seq.length s /\
                    (forall (j: nat). j + 1 < Seq.length s ==> link_at nx h (Seq.index s j) == Seq.index s (j + 1)))
          (ensures walk nx h (Seq.index s i) (Seq.length s - i) == Seq.slice s i (Seq.length s))
          (decreases Seq.length s - i)
  = let n = Seq.length s in
    if i + 1 = n then
      Seq.lemma_eq_intro (walk nx h (Seq.index s i) (n - i)) (Seq.slice s i n)
    else begin
      walk_from nx h s (i + 1);
      Seq.lemma_eq_intro (walk nx h (Seq.index s i) (n - i)) (Seq.slice s i n)
    end

/// A ring is the walk from its first box.
let walk_ring (#a: Type0) (nx pv: a -> B.box a) (h: heap a) (s: Seq.seq (B.box a))
  : Lemma (requires linked nx pv h s /\ Seq.length s > 0)
          (ensures walk nx h (Seq.index s 0) (Seq.length s) == s)
  = walk_from nx h s 0;
    Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s

(* ------------------------------------------------------------------------------------ *)
(* Views: items and owners                                                                *)
(* ------------------------------------------------------------------------------------ *)

/// The item of each box of `s`, in order; the sequence stops at a box the heap does not hold.
let rec items_of (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (h: heap a) (s: Seq.seq (B.box a))
  : Tot (Seq.seq t) (decreases Seq.length s)
  = if Seq.length s = 0 then Seq.empty
    else match lookup h (Seq.index s 0) with
         | Some r -> Seq.cons (fst (view (Seq.index s 0) r)) (items_of view h (Seq.tail s))
         | None -> Seq.empty

let item_at (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (h: heap a) (x: B.box a { mem h x }) : t =
  fst (view x (get h x))

let owner_at (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (h: heap a) (x: B.box a) : B.box b =
  match lookup h x with
  | Some r -> snd (view x r)
  | None -> B.null

let rec items_of_spec (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (h: heap a) (s: Seq.seq (B.box a))
  : Lemma (requires all_mem h s)
          (ensures Seq.length (items_of view h s) == Seq.length s /\
                   (forall (i: nat). i < Seq.length s ==>
                      Seq.index (items_of view h s) i == item_at view h (Seq.index s i)))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      assert (forall (i: nat). i < Seq.length (Seq.tail s) ==> Seq.index (Seq.tail s) i == Seq.index s (i + 1));
      items_of_spec view h (Seq.tail s)
    end

/// The boxes of the heap that `o` owns are exactly those of `s`.
[@@"opaque_to_smt"]
let owned (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (h: heap a) (s: Seq.seq (B.box a)) (o: B.box b) : prop =
  forall (x: B.box a). mem h x ==> (owner_at view h x == o <==> in_seq s x)

/// Every box of the heap but `x` holds what it held, and `x` is still held.
let frame (#a: Type0) (h0 h1: heap a) (x: B.box a) : prop =
  mem h1 x /\ (forall (y: B.box a). ~ (y == x) ==> lookup h1 y == lookup h0 y)

(* ------------------------------------------------------------------------------------ *)
(* The operations a [RegionOp] names: view and links first                                *)
(* ------------------------------------------------------------------------------------ *)

/// The `n` boxes walked from `hd` are a ring.
[@@"opaque_to_smt"]
let ring_of (#a: Type0) (nx pv: a -> B.box a) (h: heap a) (hd: B.box a) (n: int) : prop =
  ring_seq nx pv h (walk nx h hd n)

/// The ring `n` boxes long from `hd`: `hd` is null exactly when it is empty.
let shape (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int) : prop =
  0 <= n /\ (n == 0 <==> B.is_null hd) /\ ring_of nx pv h hd n

/// The boxes of the ring from `hd`, in order.
let nodes (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int) : Seq.seq (B.box a) =
  walk nx h hd n

/// The items of the boxes of `s`, in order.
let items (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (s: Seq.seq (B.box a)) : Seq.seq t =
  items_of view h s

/// The item of one box, which the heap holds.
let item (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (x: B.box a { mem h x }) : t =
  item_at view h x

/// The owner a box points back to, null for a box the heap does not hold.
let owner (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (x: B.box a) : B.box b =
  owner_at view h x

/// The owner's invariant: a ring, whose boxes are exactly those the heap says `o` owns.
let ring (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int) (o: B.box b) : prop =
  shape view nx pv h hd n /\ owned view h (walk nx h hd n) o

/// Where `InsertBefore(node, …)` puts the new box: before `node`, or last when `node` is the first.
let ins_index (#a: Type0) (s: Seq.seq (B.box a)) (node: B.box a) : int =
  let i = pos s node in if i <= 0 then Seq.length s else i

/// Every box keeps its view, and the heap holds the same boxes.
[@@"opaque_to_smt"]
let views_kept (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1: heap a) : prop =
  (forall (x: B.box a). mem h1 x <==> mem h0 x) /\
  (forall (x: B.box a). mem h0 x ==> view x (get h1 x) == view x (get h0 x))

/// `x` is detached: its links are null, it has no owner and keeps its item; every other box is as it was.
let detached (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1: heap a) (x: B.box a) : prop =
  mem h0 x /\ frame h0 h1 x /\
  B.is_null (link_at nx h1 x) /\ B.is_null (link_at pv h1 x) /\ B.is_null (owner_at view h1 x) /\
  item_at view h1 x == item_at view h0 x

(* ------------------------------------------------------------------------------------ *)
(* Lemmas                                                                                 *)
(* ------------------------------------------------------------------------------------ *)

let shape_def (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int)
  : Lemma (shape view nx pv h hd n <==>
           (0 <= n /\ (n == 0 <==> B.is_null hd) /\ ring_seq nx pv h (walk nx h hd n)))
  = reveal_opaque (`%ring_of) (ring_of nx pv h hd n)

let owned_def (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (h: heap a) (s: Seq.seq (B.box a)) (o: B.box b)
  : Lemma (owned view h s o <==> (forall (x: B.box a). mem h x ==> (owner_at view h x == o <==> in_seq s x)))
  = reveal_opaque (`%owned) (owned view h s o)

let views_kept_def (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a) (h0 h1: heap a)
  : Lemma (views_kept view nx pv h0 h1 <==>
           ((forall (x: B.box a). mem h1 x <==> mem h0 x) /\
            (forall (x: B.box a). mem h0 x ==> view x (get h1 x) == view x (get h0 x))))
  = reveal_opaque (`%views_kept) (views_kept view nx pv h0 h1)

let walk_head (#a: Type0) (nx: a -> B.box a) (h: heap a) (hd: B.box a) (n: int)
  : Lemma (requires n > 0) (ensures Seq.index (walk nx h hd n) 0 == hd)
  = ()

/// An empty ring, in a heap of whose boxes `o` owns none.
let empty (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (o: B.box b)
  : Lemma (requires forall (x: B.box a). mem h x ==> ~ (owner_at view h x == o))
          (ensures ring view nx pv h B.null 0 o /\ nodes view nx pv h B.null 0 == Seq.empty /\
                   items view nx pv h Seq.empty == Seq.empty)
  = Seq.lemma_eq_intro (walk nx h B.null 0) Seq.empty;
    shape_def view nx pv h B.null 0;
    owned_def view h (walk nx h B.null 0) o

/// A heap that holds what `h0` held at every box `h0` holds keeps its rings.
let extended (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1: heap a) (hd: B.box a) (n: int)
  : Lemma (requires shape view nx pv h0 hd n /\ (forall (x: B.box a). mem h0 x ==> lookup h1 x == lookup h0 x))
          (ensures shape view nx pv h1 hd n /\ walk nx h1 hd n == walk nx h0 hd n /\
                   items_of view h1 (walk nx h0 hd n) == items_of view h0 (walk nx h0 hd n))
  = let s = walk nx h0 hd n in
    shape_def view nx pv h0 hd n;
    shape_def view nx pv h1 hd n;
    if n = 0 then Seq.lemma_eq_intro (walk nx h1 hd n) s
    else begin
      walk_ring nx pv h1 s;
      items_of_spec view h0 s;
      items_of_spec view h1 s;
      Seq.lemma_eq_intro (items_of view h1 s) (items_of view h0 s)
    end

/// A box of a ring is held, and so are its neighbours, which are in the ring.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let neighbours (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int) (x: B.box a)
  : Lemma (requires shape view nx pv h hd n /\ pos (walk nx h hd n) x >= 0)
          (ensures (let s = walk nx h hd n in
                    let i = pos s x in
                    Seq.length s == n /\ 0 <= i /\ i < n /\ Seq.index s i == x /\
                    mem h x /\ mem h (link_at nx h x) /\ mem h (link_at pv h x) /\
                    link_at nx h x == Seq.index s (if i + 1 = n then 0 else i + 1) /\
                    link_at pv h x == Seq.index s (if i = 0 then n - 1 else i - 1) /\
                    pos s (link_at nx h x) >= 0 /\ pos s (link_at pv h x) >= 0))
  = let s = walk nx h hd n in
    let i = pos s x in
    shape_def view nx pv h hd n;
    pos_spec s x;
    pos_spec s (link_at nx h x);
    pos_spec s (link_at pv h x);
    assert (link_at nx h (Seq.index s i) == Seq.index s (if i + 1 = n then 0 else i + 1));
    if i = 0 then () else assert (link_at pv h (Seq.index s ((i - 1) + 1)) == Seq.index s (i - 1));
    assert (link_at pv h (Seq.index s i) == Seq.index s (if i = 0 then n - 1 else i - 1));
    pos_index s (if i + 1 = n then 0 else i + 1);
    pos_index s (if i = 0 then n - 1 else i - 1)
#pop-options

/// What `InsertBefore` leaves: `nw` linked in between `node` and the box before it, every
/// other link and every view as it was.
let inserted_heap (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1: heap a) (node nw: B.box a) : prop =
  let prev = link_at pv h0 node in
  (forall (y: B.box a). mem h1 y <==> mem h0 y) /\
  (forall (y: B.box a). mem h0 y ==> view y (get h1 y) == view y (get h0 y)) /\
  (forall (y: B.box a). mem h0 y /\ ~ (y == nw) /\ ~ (y == prev) ==> nx (get h1 y) == nx (get h0 y)) /\
  (forall (y: B.box a). mem h0 y /\ ~ (y == nw) /\ ~ (y == node) ==> pv (get h1 y) == pv (get h0 y)) /\
  mem h0 nw /\ mem h0 node /\ mem h0 prev /\
  nx (get h1 nw) == node /\ pv (get h1 nw) == prev /\ nx (get h1 prev) == nw /\ pv (get h1 node) == nw

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let insert_linked (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1: heap a) (s0: Seq.seq (B.box a)) (k: nat) (nw: B.box a)
  : Lemma (requires ring_seq nx pv h0 s0 /\ 0 < k /\ k <= Seq.length s0 /\ ~ (in_seq s0 nw) /\ ~ (B.is_null nw) /\
                    Seq.index s0 (if k = Seq.length s0 then 0 else k) == Seq.index s0 (if k = Seq.length s0 then 0 else k) /\
                    inserted_heap view nx pv h0 h1 (Seq.index s0 (if k = Seq.length s0 then 0 else k)) nw /\
                    link_at pv h0 (Seq.index s0 (if k = Seq.length s0 then 0 else k)) == Seq.index s0 (k - 1))
          (ensures ring_seq nx pv h1 (insert_at s0 k nw))
  = let n = Seq.length s0 in
    let s1 = insert_at s0 k nw in
    let node = Seq.index s0 (if k = n then 0 else k) in
    let prev = Seq.index s0 (k - 1) in
    insert_at_spec s0 k nw;
    assert (forall (i: nat). i < n ==> mem h0 (Seq.index s0 i));
    assert (forall (i: nat). i < n ==> ~ (Seq.index s0 i == nw));
    introduce forall (i: nat). i < n + 1 ==> mem h1 (Seq.index s1 i)
    with introduce _ ==> _ with ();
    introduce forall (i j: nat). i < n + 1 /\ j < n + 1 /\ Seq.index s1 i == Seq.index s1 j ==> i == j
    with introduce _ ==> _ with ();
    introduce forall (i: nat). i < n + 1 ==> ~ (B.is_null (Seq.index s1 i))
    with introduce _ ==> _ with ();
    introduce forall (i: nat). i + 1 < n + 1 ==>
         link_at nx h1 (Seq.index s1 i) == Seq.index s1 (i + 1) /\
         link_at pv h1 (Seq.index s1 (i + 1)) == Seq.index s1 i
    with introduce _ ==> _ with begin
      if i + 1 < k then begin
        assert (link_at nx h0 (Seq.index s0 i) == Seq.index s0 (i + 1));
        assert (link_at pv h0 (Seq.index s0 (i + 1)) == Seq.index s0 i)
      end
      else if i + 1 = k then ()
      else if i = k then ()
      else begin
        assert (link_at nx h0 (Seq.index s0 (i - 1)) == Seq.index s0 i);
        assert (link_at pv h0 (Seq.index s0 i) == Seq.index s0 (i - 1))
      end
    end;
    assert (link_at nx h0 (Seq.index s0 (n - 1)) == Seq.index s0 0);
    assert (link_at pv h0 (Seq.index s0 0) == Seq.index s0 (n - 1))
#pop-options

/// `InsertBefore(node, nw)` on a nonempty ring: the ring, with `nw` where `ins_index` puts it.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let inserted (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1: heap a) (hd: B.box a) (n: int) (node nw: B.box a)
  : Lemma (requires shape view nx pv h0 hd n /\ pos (walk nx h0 hd n) node >= 0 /\
                    mem h0 nw /\ ~ (B.is_null nw) /\ pos (walk nx h0 hd n) nw < 0 /\
                    inserted_heap view nx pv h0 h1 node nw)
          (ensures shape view nx pv h1 hd (n + 1) /\ views_kept view nx pv h0 h1 /\
                   walk nx h1 hd (n + 1) == insert_at (walk nx h0 hd n) (ins_index (walk nx h0 hd n) node) nw)
  = let s0 = walk nx h0 hd n in
    shape_def view nx pv h0 hd n;
    shape_def view nx pv h1 hd (n + 1);
    views_kept_def view nx pv h0 h1;
    neighbours view nx pv h0 hd n node;
    pos_spec s0 nw;
    let k = ins_index s0 node in
    assert (k > 0 /\ k <= n);
    assert (Seq.index s0 (if k = n then 0 else k) == node);
    insert_linked view nx pv h0 h1 s0 k nw;
    let s1 = insert_at s0 k nw in
    insert_at_spec s0 k nw;
    walk_ring nx pv h1 s1;
    walk_head nx h0 hd n;
    assert (Seq.index s1 0 == hd)
#pop-options

/// One write of links: only `x` changes, and it keeps its view.
let relinked (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1: heap a) (x: B.box a) : prop =
  mem h0 x /\ frame h0 h1 x /\ view x (get h1 x) == view x (get h0 x)

/// `InsertBefore(node, nw)` as three writes: `nw`'s links (`h1`), then the next link of the
/// box before `node` (`h2`), then `node`'s previous link (`h3`).
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let inserted3 (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1 h2 h3: heap a) (hd: B.box a) (n: int) (node nw: B.box a)
  : Lemma (requires shape view nx pv h0 hd n /\ pos (walk nx h0 hd n) node >= 0 /\
                    mem h0 nw /\ ~ (B.is_null nw) /\ pos (walk nx h0 hd n) nw < 0 /\
                    relinked view nx pv h0 h1 nw /\
                    link_at nx h1 nw == node /\ link_at pv h1 nw == link_at pv h0 node /\
                    relinked view nx pv h1 h2 (link_at pv h0 node) /\
                    link_at nx h2 (link_at pv h0 node) == nw /\
                    link_at pv h2 (link_at pv h0 node) == link_at pv h1 (link_at pv h0 node) /\
                    relinked view nx pv h2 h3 node /\
                    link_at pv h3 node == nw /\ link_at nx h3 node == link_at nx h2 node)
          (ensures shape view nx pv h3 hd (n + 1) /\ views_kept view nx pv h0 h3 /\
                   walk nx h3 hd (n + 1) == insert_at (walk nx h0 hd n) (ins_index (walk nx h0 hd n) node) nw)
  = neighbours view nx pv h0 hd n node;
    pos_spec (walk nx h0 hd n) nw;
    let prev = link_at pv h0 node in
    assert (~ (nw == node) /\ ~ (nw == prev));
    assert (inserted_heap view nx pv h0 h3 node nw);
    inserted view nx pv h0 h3 hd n node nw
#pop-options

let in_seq_insert_at (#a: Type0) (s: Seq.seq (B.box a)) (k: int) (x y: B.box a)
  : Lemma (requires 0 <= k /\ k <= Seq.length s)
          (ensures in_seq (insert_at s k x) y <==> (y == x \/ in_seq s y))
  = insert_at_spec s k x;
    let s1 = insert_at s k x in
    introduce forall (i: nat). i < Seq.length s1 /\ Seq.index s1 i == y ==> (y == x \/ in_seq s y)
    with introduce _ ==> _ with (if i < k then () else if i = k then () else assert (Seq.index s (i - 1) == y));
    introduce forall (i: nat). i < Seq.length s /\ Seq.index s i == y ==> in_seq s1 y
    with introduce _ ==> _ with (if i < k then assert (Seq.index s1 i == y) else assert (Seq.index s1 (i + 1) == y));
    assert (Seq.index s1 k == x)

/// A box allocated into the heap of a ring is not in it; the ring and its items are unchanged.
let allocated (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 ha: heap a) (hd: B.box a) (n: int) (nw: B.box a)
  : Lemma (requires shape view nx pv h0 hd n /\ ~ (mem h0 nw) /\ mem ha nw /\
                    (forall (y: B.box a). mem h0 y ==> lookup ha y == lookup h0 y))
          (ensures shape view nx pv ha hd n /\ walk nx ha hd n == walk nx h0 hd n /\
                   items_of view ha (walk nx h0 hd n) == items_of view h0 (walk nx h0 hd n) /\
                   pos (walk nx ha hd n) nw < 0)
  = extended view nx pv h0 ha hd n;
    shape_def view nx pv h0 hd n;
    pos_spec (walk nx h0 hd n) nw

/// The ring a new box `nw`, allocated owned by `o` (heap `ha`), was inserted into at `k`
/// (heap `h1`, its views kept): `o`'s ring, with `nw`'s item at `k`.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let adopted (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 ha h1: heap a) (hd0: B.box a) (n0: int) (hd1 nw: B.box a) (k: int) (o: B.box b)
  : Lemma (requires ring view nx pv h0 hd0 n0 o /\ ~ (mem h0 nw) /\ mem ha nw /\
                    (forall (y: B.box a). mem h0 y ==> lookup ha y == lookup h0 y) /\
                    (forall (y: B.box a). mem ha y ==> mem h0 y \/ y == nw) /\
                    owner_at view ha nw == o /\
                    shape view nx pv h1 hd1 (n0 + 1) /\ views_kept view nx pv ha h1 /\
                    0 <= k /\ k <= n0 /\
                    walk nx h1 hd1 (n0 + 1) == insert_at (walk nx h0 hd0 n0) k nw)
          (ensures ring view nx pv h1 hd1 (n0 + 1) o /\
                   items_of view h1 (walk nx h1 hd1 (n0 + 1)) ==
                     insert_at (items_of view h0 (walk nx h0 hd0 n0)) k (item_at view ha nw))
  = let s0 = walk nx h0 hd0 n0 in
    let s1 = walk nx h1 hd1 (n0 + 1) in
    shape_def view nx pv h0 hd0 n0;
    shape_def view nx pv h1 hd1 (n0 + 1);
    owned_def view h0 s0 o;
    owned_def view h1 s1 o;
    views_kept_def view nx pv ha h1;
    insert_at_spec s0 k nw;
    introduce forall (x: B.box a). mem h1 x ==> (owner_at view h1 x == o <==> in_seq s1 x)
    with introduce _ ==> _ with begin
      in_seq_insert_at s0 k nw x;
      assert (owner_at view h1 x == owner_at view ha x)
    end;
    items_of_spec view h0 s0;
    items_of_spec view h1 s1;
    let i0 = items_of view h0 s0 in
    insert_at_spec i0 k (item_at view ha nw);
    introduce forall (j: nat). j < n0 + 1 ==>
        Seq.index (items_of view h1 s1) j == Seq.index (insert_at i0 k (item_at view ha nw)) j
    with introduce _ ==> _ with begin
      assert (item_at view h1 (Seq.index s1 j) == item_at view ha (Seq.index s1 j))
    end;
    Seq.lemma_eq_intro (items_of view h1 s1) (insert_at i0 k (item_at view ha nw))
#pop-options

/// A ring entered at its last box: that box, then the rest in order.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let rotate_last (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int)
  : Lemma (requires shape view nx pv h hd n /\ n > 0)
          (ensures (let s = walk nx h hd n in
                    shape view nx pv h (Seq.index s (n - 1)) n /\
                    walk nx h (Seq.index s (n - 1)) n == Seq.cons (Seq.index s (n - 1)) (Seq.slice s 0 (n - 1))))
  = let s = walk nx h hd n in
    shape_def view nx pv h hd n;
    let l = Seq.index s (n - 1) in
    let s' = Seq.cons l (Seq.slice s 0 (n - 1)) in
    shape_def view nx pv h l n;
    assert (forall (i: nat). i < n ==> Seq.index s' i == (if i = 0 then l else Seq.index s (i - 1)));
    introduce forall (i: nat). i + 1 < n ==>
        link_at nx h (Seq.index s' i) == Seq.index s' (i + 1) /\ link_at pv h (Seq.index s' (i + 1)) == Seq.index s' i
    with introduce _ ==> _ with (if i = 0 then () else assert (link_at nx h (Seq.index s (i - 1)) == Seq.index s i));
    assert (ring_seq nx pv h s');
    walk_ring nx pv h s'
#pop-options

/// `AddFirst` is `AddLast` and then the head moved to the new box.
let rotated (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int) (s0: Seq.seq (B.box a)) (nw: B.box a)
  : Lemma (requires shape view nx pv h hd (n + 1) /\ Seq.length s0 == n /\ n >= 0 /\
                    walk nx h hd (n + 1) == insert_at s0 n nw)
          (ensures shape view nx pv h nw (n + 1) /\ walk nx h nw (n + 1) == insert_at s0 0 nw)
  = rotate_last view nx pv h hd (n + 1);
    insert_at_spec s0 n nw;
    insert_at_spec s0 0 nw;
    let s = walk nx h hd (n + 1) in
    Seq.lemma_eq_intro (Seq.slice s 0 n) s0;
    Seq.lemma_eq_intro (Seq.cons nw s0) (insert_at s0 0 nw)

/// One box linked to itself: the ring of one.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let single (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h0 h1: heap a) (hd: B.box a) (n: int) (nw: B.box a)
  : Lemma (requires n == 0 /\ ~ (B.is_null nw) /\ relinked view nx pv h0 h1 nw /\
                    link_at nx h1 nw == nw /\ link_at pv h1 nw == nw)
          (ensures shape view nx pv h1 nw 1 /\ views_kept view nx pv h0 h1 /\
                   walk nx h1 nw 1 == insert_at (walk nx h0 hd n) 0 nw)
  = shape_def view nx pv h1 nw 1;
    shape_def view nx pv h0 hd n;
    views_kept_def view nx pv h0 h1;
    let s = walk nx h1 nw 1 in
    assert (Seq.length s == 1 /\ Seq.index s 0 == nw);
    insert_at_spec (walk nx h0 hd n) 0 nw;
    Seq.lemma_eq_intro s (insert_at (walk nx h0 hd n) 0 nw)
#pop-options

/// Inserting before the first box of a nonempty ring puts the new box last.
let ins_head (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int)
  : Lemma (requires shape view nx pv h hd n /\ n > 0)
          (ensures mem h hd /\ pos (walk nx h hd n) hd == 0 /\ ins_index (walk nx h hd n) hd == n)
  = shape_def view nx pv h hd n;
    walk_head nx h hd n;
    pos_index (walk nx h hd n) 0

/// The first box of a ring is its head, held, and the last is the one before it.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let ends (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int)
  : Lemma (requires shape view nx pv h hd n)
          (ensures Seq.length (walk nx h hd n) == n /\
                   (n > 0 ==> mem h hd /\ Seq.index (walk nx h hd n) 0 == hd /\
                              Seq.index (walk nx h hd n) (n - 1) == link_at pv h hd))
  = shape_def view nx pv h hd n;
    if n > 0 then walk_head nx h hd n
#pop-options

/// A ring has an item per box (for a model's refinement, R31.7).
let items_length (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a)
    (h: heap a) (hd: B.box a) (n: int)
  : Lemma (requires shape view nx pv h hd n)
          (ensures Seq.length (items view nx pv h (nodes view nx pv h hd n)) == n)
          [SMTPat (items view nx pv h (nodes view nx pv h hd n))]
  = shape_def view nx pv h hd n;
    items_of_spec view h (walk nx h hd n)

/// A new owner's empty region is its empty ring (R31.7).
let empty_ring (#a #t #b: Type0) (view: B.box a -> a -> (t & B.box b)) (nx pv: a -> B.box a) (o: B.box b)
  : Lemma (ring view nx pv ([] <: heap a) B.null 0 o)
          [SMTPat (ring view nx pv ([] <: heap a) B.null 0 o)]
  = empty view nx pv ([] <: heap a) o
