module Pulse.Lib.CSharp.SearchTree

/// The comparer-directed searches of a binary search tree whose nodes carry a key and a
/// tag (a red-black tree's colour) (doc/translation.md R27.9). Each function follows the
/// path the code follows, so what it says needs no ordering hypothesis: it is what the
/// search returns, whatever the tree.

module O = Pulse.Lib.CSharp.Order
module T = Pulse.Lib.CSharp.Tree

/// Whether the search for `x` ends at a node whose key compares equal to it.
let rec contains (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a)
  : Tot bool (decreases t)
  = match t with
    | T.Leaf -> false
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then true else if o < 0 then contains c l x else contains c r x

/// The key the search for `x` ends at, or `d` when it ends at a leaf.
let rec find (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a) (d: a)
  : Tot a (decreases t)
  = match t with
    | T.Leaf -> d
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then v else if o < 0 then find c l x d else find c r x d

/// The key at the root, or `d` in the empty tree (R27.13).
let root_key (#a #b: Type0) (t: T.tree (a & b)) (d: a) : a =
  match t with
  | T.Leaf -> d
  | T.Branch _ (v, _) _ -> v

/// The leftmost key, or `d` in the empty tree.
let rec leftmost (#a #b: Type0) (t: T.tree (a & b)) (d: a) : Tot a (decreases t) =
  match t with
  | T.Leaf -> d
  | T.Branch T.Leaf (v, _) _ -> v
  | T.Branch l _ _ -> leftmost l d

/// The rightmost key, or `d` in the empty tree.
let rec rightmost (#a #b: Type0) (t: T.tree (a & b)) (d: a) : Tot a (decreases t) =
  match t with
  | T.Leaf -> d
  | T.Branch _ (v, _) T.Leaf -> v
  | T.Branch _ _ r -> rightmost r d

/// The position of the node the search for `x` ends at, numbering the tree breadth-first
/// as an implicit binary heap is numbered (the root of a subtree being `k`), or -1.
let rec heap_index (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a) (k: int)
  : Tot int (decreases t)
  = match t with
    | T.Leaf -> -1
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then k
      else if o < 0 then heap_index c l x (2 * k + 1)
      else heap_index c r x (2 * k + 2)

(* ---------------------------------------------------------------------------------- *)
(* R27.11. The set a search tree holds, and the red-black invariants.                   *)

module Seq = FStar.Seq
module S = Pulse.Lib.CSharp.Sorted

/// The keys in order: the set's model, once they are strictly sorted.
let rec keys (#a #b: Type0) (t: T.tree (a & b)) : Tot (Seq.seq a) (decreases t) =
  match t with
  | T.Leaf -> Seq.empty
  | T.Branch l (v, _) r -> Seq.append (keys l) (Seq.cons v (keys r))

let rec keys_length (#a #b: Type0) (t: T.tree (a & b))
  : Lemma (ensures Seq.length (keys t) == T.size t) (decreases t)
          [SMTPat (Seq.length (keys t))]
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ r -> keys_length l; keys_length r

/// A node's tag is whether it is red.
/// R27.17. The colour of a red-black node, the image of `NodeColor` (`[SpecType]`): a
/// field of this type holds one of two values, where a byte would hold any of 256.
type node_color = | Black | Red

let is_red (#a: Type0) (t: T.tree (a & bool)) : bool =
  match t with
  | T.Branch _ (_, red) _ -> red
  | T.Leaf -> false

/// The number of black nodes on the leftmost path.
let rec black_height (#a: Type0) (t: T.tree (a & bool)) : Tot nat (decreases t) =
  match t with
  | T.Leaf -> 0
  | T.Branch l (_, red) _ -> black_height l + (if red then 0 else 1)

/// No red node has a red child, and every path has the same number of black nodes.
let rec rb (#a: Type0) (t: T.tree (a & bool)) : Tot bool (decreases t) =
  match t with
  | T.Leaf -> true
  | T.Branch l (_, red) r ->
    rb l && rb r && black_height l = black_height r &&
    (not red || (not (is_red l) && not (is_red r)))

/// A red-black tree: `rb`, with a black root.
let red_black (#a: Type0) (t: T.tree (a & bool)) : bool = rb t && not (is_red t)

(* R27.16. The re-shapings `SortedSet<T>.Node`'s helpers perform, as functions of the tree. *)

/// The tree with its root's colour set.
let recolor (#a: Type0) (t: T.tree (a & bool)) (red: bool) : T.tree (a & bool) =
  match t with
  | T.Leaf -> T.Leaf
  | T.Branch l (k, _) r -> T.Branch l (k, red) r

/// The root's right child becomes the root.
let rot_left (#a: Type0) (t: T.tree a) : T.tree a =
  match t with
  | T.Branch x v (T.Branch y w z) -> T.Branch (T.Branch x v y) w z
  | _ -> t

/// The root's left child becomes the root.
let rot_right (#a: Type0) (t: T.tree a) : T.tree a =
  match t with
  | T.Branch (T.Branch x v y) w z -> T.Branch x v (T.Branch y w z)
  | _ -> t

/// The left child rotated left, then the root rotated right.
let rot_left_right (#a: Type0) (t: T.tree a) : T.tree a =
  match t with
  | T.Branch l v r -> rot_right (T.Branch (rot_left l) v r)
  | _ -> t

/// The right child rotated right, then the root rotated left.
let rot_right_left (#a: Type0) (t: T.tree a) : T.tree a =
  match t with
  | T.Branch l v r -> rot_left (T.Branch l v (rot_right r))
  | _ -> t

/// A 4-node split: the root red, its children black.
let split4 (#a: Type0) (t: T.tree (a & bool)) : T.tree (a & bool) =
  match t with
  | T.Leaf -> T.Leaf
  | T.Branch l (k, _) r -> T.Branch (recolor l false) (k, true) (recolor r false)

/// Two 2-nodes merged: the root black, its children red.
let merge2 (#a: Type0) (t: T.tree (a & bool)) : T.tree (a & bool) =
  match t with
  | T.Leaf -> T.Leaf
  | T.Branch l (k, _) r -> T.Branch (recolor l true) (k, false) (recolor r true)

/// R27.17. The image of `TreeRotation` (`[SpecType]`, each constant renamed by `[SpecCase]`).
type tree_rotation = | RotLeft | RotLeftRight | RotRight | RotRightLeft

/// R27.17. `Node.Rotate`: a single rotation blackens the red grandchild it lifts.
let rotate (#a: Type0) (r: tree_rotation) (t: T.tree (a & bool)) : T.tree (a & bool) =
  match r, t with
  | RotRight, T.Branch (T.Branch ll lv lr) v rr -> rot_right (T.Branch (T.Branch (recolor ll false) lv lr) v rr)
  | RotLeft, T.Branch l v (T.Branch rl rv rr) -> rot_left (T.Branch l v (T.Branch rl rv (recolor rr false)))
  | RotLeftRight, _ -> rot_left_right t
  | RotRightLeft, _ -> rot_right_left t
  | _, _ -> t

/// R27.17. The grandchild the rotation lifts is red.
let can_rotate (#a: Type0) (r: tree_rotation) (t: T.tree (a & bool)) : bool =
  match r with
  | RotRight -> is_red (T.left (T.left t))
  | RotLeft -> is_red (T.right (T.right t))
  | RotLeftRight -> is_red (T.right (T.left t))
  | RotRightLeft -> is_red (T.left (T.right t))

let keys_recolor (#a: Type0) (t: T.tree (a & bool)) (red: bool)
  : Lemma (ensures keys (recolor t red) == keys t) [SMTPat (keys (recolor t red))]
  = ()

let keys_rot_left (#a #b: Type0) (t: T.tree (a & b))
  : Lemma (ensures keys (rot_left t) == keys t) [SMTPat (keys (rot_left t))]
  = match t with
    | T.Branch x _ (T.Branch y _ z) ->
      Seq.lemma_eq_intro (keys (rot_left t)) (keys t)
    | _ -> ()

let keys_rot_right (#a #b: Type0) (t: T.tree (a & b))
  : Lemma (ensures keys (rot_right t) == keys t) [SMTPat (keys (rot_right t))]
  = match t with
    | T.Branch (T.Branch x _ y) _ z ->
      Seq.lemma_eq_intro (keys (rot_right t)) (keys t)
    | _ -> ()

let keys_split4 (#a: Type0) (t: T.tree (a & bool))
  : Lemma (ensures keys (split4 t) == keys t) [SMTPat (keys (split4 t))]
  = ()

let keys_merge2 (#a: Type0) (t: T.tree (a & bool))
  : Lemma (ensures keys (merge2 t) == keys t) [SMTPat (keys (merge2 t))]
  = ()

let below_all (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (v: a) : prop =
  forall (i: nat). i < Seq.length s ==> O.compare c (Seq.index s i) v < 0

let above_all (#a: Type0) (c: O.comparer a) (v: a) (s: Seq.seq a) : prop =
  forall (i: nat). i < Seq.length s ==> O.compare c v (Seq.index s i) < 0

let index_pivot (#a: Type0) (sl: Seq.seq a) (v: a) (sr: Seq.seq a) (i: nat)
  : Lemma (ensures i < Seq.length (Seq.append sl (Seq.cons v sr)) ==>
                   Seq.index (Seq.append sl (Seq.cons v sr)) i ==
                   (if i < Seq.length sl then Seq.index sl i
                    else if i = Seq.length sl then v
                    else Seq.index sr (i - Seq.length sl - 1)))
  = ()

/// A node's keys are strictly sorted exactly when its subtrees' are and the key separates them.
let sorted_pivot (#a: Type0) (c: O.comparer a) (sl: Seq.seq a) (v: a) (sr: Seq.seq a)
  : Lemma (S.strictly_sorted c (Seq.append sl (Seq.cons v sr)) <==>
           (S.strictly_sorted c sl /\ S.strictly_sorted c sr /\
            below_all c sl v /\ above_all c v sr))
  = let s = Seq.append sl (Seq.cons v sr) in
    let n = Seq.length sl in
    FStar.Classical.forall_intro (index_pivot sl v sr);
    let fwd () : Lemma (requires S.strictly_sorted c s)
                       (ensures S.strictly_sorted c sl /\ S.strictly_sorted c sr /\
                                below_all c sl v /\ above_all c v sr)
      = assert (forall (i: nat). i < n ==> Seq.index s i == Seq.index sl i);
        assert (forall (i: nat). i < Seq.length sr ==> Seq.index s (n + 1 + i) == Seq.index sr i);
        assert (Seq.index s n == v)
    in
    let bwd () : Lemma (requires S.strictly_sorted c sl /\ S.strictly_sorted c sr /\
                                 below_all c sl v /\ above_all c v sr)
                       (ensures S.strictly_sorted c s)
      = let aux (i j: nat)
          : Lemma (ensures i < j /\ j < Seq.length s ==> O.compare c (Seq.index s i) (Seq.index s j) < 0)
          = if not (i < j && j < Seq.length s) then ()
            else if j < n then ()
            else if i < n && j = n then ()
            else if i = n then ()
            else if i < n then
              O.compare_trans c (Seq.index sl i) v (Seq.index sr (j - n - 1))
            else ()
        in
        FStar.Classical.forall_intro_2 aux
    in
    FStar.Classical.move_requires fwd ();
    FStar.Classical.move_requires bwd ()

let sorted_branch (#a #b: Type0) (c: O.comparer a) (l: T.tree (a & b)) (v: a) (g: b) (r: T.tree (a & b))
  : Lemma (S.strictly_sorted c (keys (T.Branch l (v, g) r)) <==>
           (S.strictly_sorted c (keys l) /\ S.strictly_sorted c (keys r) /\
            below_all c (keys l) v /\ above_all c v (keys r)))
          [SMTPat (S.strictly_sorted c (keys (T.Branch l (v, g) r)))]
  = sorted_pivot c (keys l) v (keys r)

let rec lower_bound_append (#a: Type0) (c: O.comparer a) (s1 s2: Seq.seq a) (x: a)
  : Lemma (ensures S.lower_bound c (Seq.append s1 s2) x == S.lower_bound c s1 x + S.lower_bound c s2 x)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then assert (Seq.equal (Seq.append s1 s2) s2)
    else (assert (Seq.equal (Seq.tail (Seq.append s1 s2)) (Seq.append (Seq.tail s1) s2));
          lower_bound_append c (Seq.tail s1) s2 x)

let rec lower_bound_all_below (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x: a)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> O.compare c (Seq.index s i) x < 0)
          (ensures S.lower_bound c s x == Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then () else lower_bound_all_below c (Seq.tail s) x

let rec lower_bound_all_above (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x: a)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> O.compare c (Seq.index s i) x >= 0)
          (ensures S.lower_bound c s x == 0)
          (decreases Seq.length s)
  = if Seq.length s = 0 then () else lower_bound_all_above c (Seq.tail s) x

/// Where the search for `x` goes in a node whose keys are sorted: the position the node's
/// key or one of its subtrees gives, shifted to the node's sequence.
let lower_bound_pivot (#a: Type0) (c: O.comparer a) (sl: Seq.seq a) (v: a) (sr: Seq.seq a) (x: a)
  : Lemma (requires below_all c sl v /\ above_all c v sr)
          (ensures (let lb = S.lower_bound c (Seq.append sl (Seq.cons v sr)) x in
                    let o = O.compare c x v in
                    (o = 0 ==> lb == Seq.length sl) /\
                    (o < 0 ==> lb == S.lower_bound c sl x) /\
                    (o > 0 ==> lb == Seq.length sl + 1 + S.lower_bound c sr x)))
  = let o = O.compare c x v in
    lower_bound_append c sl (Seq.cons v sr) x;
    lower_bound_append c (Seq.create 1 v) sr x;
    assert (Seq.equal (Seq.cons v sr) (Seq.append (Seq.create 1 v) sr));
    assert (S.lower_bound c (Seq.tail (Seq.create 1 v)) x == 0);
    let gt_v (y: a) : Lemma (requires O.compare c v y < 0 /\ o <= 0) (ensures O.compare c y x > 0)
      = O.compare_antisym c x v; O.compare_antisym c y x;
        O.compare_trans c x v y; O.compare_antisym c x y in
    let lt_v (y: a) : Lemma (requires O.compare c y v < 0 /\ o >= 0) (ensures O.compare c y x < 0)
      = O.compare_antisym c x v; O.compare_trans c y v x in
    if o <= 0 then begin
      FStar.Classical.forall_intro (FStar.Classical.move_requires gt_v);
      lower_bound_all_above c sr x
    end;
    if o >= 0 then begin
      FStar.Classical.forall_intro (FStar.Classical.move_requires lt_v);
      lower_bound_all_below c sl x
    end

/// R27.11. On a tree whose keys are strictly sorted, the search finds exactly the members:
/// the node it ends at holds the key at `x`'s position in the in-order sequence.
let rec find_keys (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x d: a)
  : Lemma (requires S.strictly_sorted c (keys t))
          (ensures (let i = S.key_index c (keys t) x in
                    contains c t x == (i >= 0) /\
                    find c t x d == (if i >= 0 then Seq.index (keys t) i else d)))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, g) r ->
      let sl = keys l in
      let sr = keys r in
      let n = Seq.length sl in
      sorted_pivot c sl v sr;
      lower_bound_pivot c sl v sr x;
      FStar.Classical.forall_intro (index_pivot sl v sr);
      let o = O.compare c x v in
      O.compare_antisym c x v;
      if o = 0 then ()
      else if o < 0 then find_keys c l x d
      else find_keys c r x d

let contains_keys (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a)
  : Lemma (requires S.strictly_sorted c (keys t))
          (ensures contains c t x == (S.key_index c (keys t) x >= 0))
          [SMTPat (contains c t x); SMTPat (S.strictly_sorted c (keys t))]
  = find_keys c t x x

let find_keys_pat (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x d: a)
  : Lemma (requires S.strictly_sorted c (keys t))
          (ensures find c t x d ==
                   (let i = S.key_index c (keys t) x in if i >= 0 then Seq.index (keys t) i else d))
          [SMTPat (find c t x d); SMTPat (S.strictly_sorted c (keys t))]
  = find_keys c t x d

let rec leftmost_keys (#a #b: Type0) (t: T.tree (a & b)) (d: a)
  : Lemma (ensures leftmost t d == (if T.size t = 0 then d else Seq.index (keys t) 0))
          (decreases t)
          [SMTPat (leftmost t d)]
  = match t with
    | T.Leaf -> ()
    | T.Branch T.Leaf _ _ -> ()
    | T.Branch l (v, _) r -> leftmost_keys l d

let rec rightmost_keys (#a #b: Type0) (t: T.tree (a & b)) (d: a)
  : Lemma (ensures rightmost t d == (if T.size t = 0 then d else Seq.index (keys t) (T.size t - 1)))
          (decreases t)
          [SMTPat (rightmost t d)]
  = match t with
    | T.Leaf -> ()
    | T.Branch _ _ T.Leaf -> ()
    | T.Branch l (v, _) r -> rightmost_keys r d

(* ---------------------------------------------------------------------------------- *)
(* R27.14. The bound on a breadth-first position: `InternalIndexOf`'s true range.        *)

/// `2^height`: one more than the number of breadth-first positions the tree's depth admits.
let breadth (#a: Type0) (t: T.tree a) : pos = pow2 (T.height t)

/// The search for a position starting at `k` in `t`, inside a tree of height `h`: every
/// position it reaches, and the next one it computes, is at most `2^(h+1) - 2`.
let index_room (#a: Type0) (k: int) (t: T.tree a) (h: int) : bool =
  0 <= k && 0 <= h && (k + 2) * pow2 (T.height t) <= pow2 (h + 1)

let index_room_init (#a: Type0) (t: T.tree a)
  : Lemma (index_room 0 t (T.height t))
          [SMTPat (index_room 0 t (T.height t))]
  = FStar.Math.Lemmas.pow2_double_mult (T.height t)

/// Below height 31 every position, and the next one computed from it, fits an `int`.
let index_room_int (#a: Type0) (k: int) (t: T.tree a) (h: int)
  : Lemma (requires index_room k t h /\ h <= 30)
          (ensures (T.Branch? t ==> 2 * k + 2 <= 2147483646) /\ pow2 h <= 1073741824)
          [SMTPat (index_room k t h)]
  = FStar.Math.Lemmas.pow2_le_compat 30 h;
    FStar.Math.Lemmas.pow2_le_compat 31 (h + 1);
    assert_norm (pow2 31 == 2147483648);
    assert_norm (pow2 30 == 1073741824);
    if T.Branch? t then begin
      FStar.Math.Lemmas.pow2_le_compat (T.height t) 1;
      FStar.Math.Lemmas.lemma_mult_le_left (k + 2) 2 (pow2 (T.height t))
    end

let index_room_step (#a: Type0) (k: int) (l: T.tree a) (v: a) (r: T.tree a) (h: int)
  : Lemma (requires index_room k (T.Branch l v r) h)
          (ensures index_room (2 * k + 1) l h /\ index_room (2 * k + 2) r h /\
                   k <= pow2 h - 2 /\ 2 * k + 2 <= pow2 (h + 1) - 2)
          [SMTPat (index_room k (T.Branch l v r) h)]
  = let n = T.height (T.Branch l v r) in
    FStar.Math.Lemmas.pow2_double_mult (n - 1);
    FStar.Math.Lemmas.pow2_le_compat (n - 1) (T.height l);
    FStar.Math.Lemmas.pow2_le_compat (n - 1) (T.height r);
    FStar.Math.Lemmas.pow2_le_compat n 1;
    FStar.Math.Lemmas.pow2_double_mult h;
    assert ((k + 2) * pow2 n == (2 * k + 4) * pow2 (n - 1));
    FStar.Math.Lemmas.lemma_mult_le_left (2 * k + 3) (pow2 (T.height l)) (pow2 (n - 1));
    FStar.Math.Lemmas.lemma_mult_le_left (2 * k + 4) (pow2 (T.height r)) (pow2 (n - 1));
    FStar.Math.Lemmas.lemma_mult_le_left (k + 2) 2 (pow2 n)

let rec heap_index_room (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a) (k h: int)
  : Lemma (requires index_room k t h)
          (ensures (let i = heap_index c t x k in
                    (i >= 0 <==> contains c t x) /\ i <= pow2 h - 2))
          (decreases t)
          [SMTPat (heap_index c t x k); SMTPat (index_room k t h)]
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, w) r ->
      index_room_step k l (v, w) r h;
      let o = O.compare c x v in
      if o = 0 then ()
      else if o < 0 then heap_index_room c l x (2 * k + 1) h
      else heap_index_room c r x (2 * k + 2) h

let heap_index_bound (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a)
  : Lemma (let i = heap_index c t x 0 in
           (i >= 0 <==> contains c t x) /\ i <= breadth t - 2)
          [SMTPat (heap_index c t x 0)]
  = index_room_init t;
    heap_index_room c t x 0 (T.height t)

(* ---------------------------------------------------------------------------------- *)
(* R27.14. Range search: `FindRange` stops at the first node, top-down, inside the bounds. *)

/// `x` is within the bounds that are active.
let in_range (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (x: a) : bool =
  (not la || O.compare c lo x <= 0) && (not ua || O.compare c hi x >= 0)

let rec any_in_range_from (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (lo hi: a) (la ua: bool) (i: nat)
  : Tot bool (decreases (Seq.length s - i))
  = if i >= Seq.length s then false
    else in_range c lo hi la ua (Seq.index s i) || any_in_range_from c s lo hi la ua (i + 1)

/// Some item of `s` is within the bounds.
let any_in_range (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (lo hi: a) (la ua: bool) : bool =
  any_in_range_from c s lo hi la ua 0

let rec any_in_range_from_exists (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (lo hi: a) (la ua: bool) (i: nat)
  : Lemma (ensures any_in_range_from c s lo hi la ua i <==>
                   (exists (j: nat). i <= j /\ j < Seq.length s /\ in_range c lo hi la ua (Seq.index s j)))
          (decreases (Seq.length s - i))
  = if i >= Seq.length s then () else any_in_range_from_exists c s lo hi la ua (i + 1)

/// Whether the top-down range search finds a node, and the key it stops at.
let rec range_hit (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Tot bool (decreases t)
  = match t with
    | T.Leaf -> false
    | T.Branch l (v, _) r ->
      if la && O.compare c lo v > 0 then range_hit c r lo hi la ua
      else if ua && O.compare c hi v < 0 then range_hit c l lo hi la ua
      else true

let rec range_hit_keys (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (requires S.strictly_sorted c (keys t))
          (ensures range_hit c t lo hi la ua <==>
                   (exists (j: nat). j < Seq.length (keys t) /\ in_range c lo hi la ua (Seq.index (keys t) j)))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, g) r ->
      let sl = keys l in
      let sr = keys r in
      let n = Seq.length sl in
      sorted_pivot c sl v sr;
      FStar.Classical.forall_intro (index_pivot sl v sr);
      let s = keys t in
      assert (forall (j: nat). j < n ==> Seq.index s j == Seq.index sl j);
      assert (forall (j: nat). j < Seq.length sr ==> Seq.index s (n + 1 + j) == Seq.index sr j);
      assert (Seq.index s n == v);
      if la && O.compare c lo v > 0 then begin
        range_hit_keys c r lo hi la ua;
        let left_out (j: nat)
          : Lemma (j <= n ==> not (in_range c lo hi la ua (Seq.index s j)))
          = if j < n then O.compare_trans c (Seq.index sl j) v lo else ()
        in
        FStar.Classical.forall_intro left_out;
        let move (j: nat)
          : Lemma (n < j /\ j < Seq.length s ==> Seq.index s j == Seq.index sr (j - n - 1))
          = ()
        in
        FStar.Classical.forall_intro move
      end
      else if ua && O.compare c hi v < 0 then begin
        range_hit_keys c l lo hi la ua;
        let right_out (j: nat)
          : Lemma (n <= j /\ j < Seq.length s ==> not (in_range c lo hi la ua (Seq.index s j)))
          = if n < j && j < Seq.length s then O.compare_trans c hi v (Seq.index sr (j - n - 1)) else ()
        in
        FStar.Classical.forall_intro right_out
      end
      else assert (in_range c lo hi la ua (Seq.index s n))

/// Under the search-tree invariant the search finds a node exactly when some item is in range.
let range_hit_any (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (requires S.strictly_sorted c (keys t))
          (ensures range_hit c t lo hi la ua == any_in_range c (keys t) lo hi la ua)
          [SMTPat (range_hit c t lo hi la ua); SMTPat (S.strictly_sorted c (keys t))]
  = range_hit_keys c t lo hi la ua;
    any_in_range_from_exists c (keys t) lo hi la ua 0
