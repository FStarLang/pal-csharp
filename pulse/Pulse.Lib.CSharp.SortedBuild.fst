module Pulse.Lib.CSharp.SortedBuild

/// R27.32. The red-black tree `SortedSet<T>.ConstructRootFromSortedArray` builds from a
/// sorted array, as a function of the array's contents (`build`), and what it is: its keys
/// are the slice in order (`keys_build`), and it is a red-black tree whose black height
/// depends only on the slice's length (`rb_build`). Everything is proved here without
/// admits.

module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module S = Pulse.Lib.CSharp.Sorted
module O = Pulse.Lib.CSharp.Order
module Seq = FStar.Seq
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module RT = Pulse.Lib.CSharp.RegionTree
open Pulse.Lib.CSharp.Region

/// A node with no children.
let leaf_of (#a: Type0) (v: a) (red: bool) : T.tree (a & bool) = T.Branch T.Leaf (v, red) T.Leaf

/// The tree `ConstructRootFromSortedArray(arr, lo, hi, red)` builds over `s[lo..hi]`: the
/// middle element at the root, black, and `red` (the node an even-sized parent call saved)
/// under the leftmost node.
let rec build (#a: Type0) (s: Seq.seq a) (lo hi: int) (red: T.tree (a & bool))
  : Tot (T.tree (a & bool)) (decreases (if hi - lo + 1 > 0 then hi - lo + 1 else 0))
  = if lo < 0 || hi >= Seq.length s || hi - lo + 1 <= 0 then T.Leaf
    else
      let size = hi - lo + 1 in
      if size = 1 then T.Branch red (Seq.index s lo, false) T.Leaf
      else if size = 2 then T.Branch red (Seq.index s lo, false) (leaf_of (Seq.index s hi) true)
      else if size = 3 then
        T.Branch (T.Branch red (Seq.index s lo, false) T.Leaf) (Seq.index s (lo + 1), false)
                 (leaf_of (Seq.index s hi) false)
      else
        let mid = (lo + hi) / 2 in
        T.Branch (build s lo (mid - 1) red) (Seq.index s mid, false)
                 (if size % 2 = 0 then build s (mid + 2) hi (leaf_of (Seq.index s (mid + 1)) true)
                  else build s (mid + 1) hi T.Leaf)

/// The black height of a built tree of `n` nodes.
let rec bhf (n: nat) : Tot nat (decreases n) = if n = 0 then 0 else bhf ((n - 1) / 2) + 1

/// What may be passed as `redNode`: nothing, or a red node with no children.
let red_arg (#a: Type0) (red: T.tree (a & bool)) : bool =
  match red with
  | T.Leaf -> true
  | T.Branch T.Leaf (_, true) T.Leaf -> true
  | _ -> false

let keys_leaf (#a: Type0) (v: a) (red: bool)
  : Lemma (ST.keys (leaf_of v red) `Seq.equal` Seq.create 1 v)
  = ()

let slice_split (#a: Type0) (s: Seq.seq a) (i j k: nat)
  : Lemma (requires i <= j /\ j <= k /\ k <= Seq.length s)
          (ensures Seq.slice s i k == Seq.append (Seq.slice s i j) (Seq.slice s j k))
  = Seq.lemma_eq_intro (Seq.slice s i k) (Seq.append (Seq.slice s i j) (Seq.slice s j k))

let slice_cons (#a: Type0) (s: Seq.seq a) (i k: nat)
  : Lemma (requires i < k /\ k <= Seq.length s)
          (ensures Seq.slice s i k == Seq.cons (Seq.index s i) (Seq.slice s (i + 1) k))
  = Seq.lemma_eq_intro (Seq.slice s i k) (Seq.cons (Seq.index s i) (Seq.slice s (i + 1) k))

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
/// The keys of a built tree: `red`'s, then the slice.
let rec keys_build (#a: Type0) (s: Seq.seq a) (lo hi: int) (red: T.tree (a & bool))
  : Lemma (requires 0 <= lo /\ lo <= hi /\ hi < Seq.length s)
          (ensures ST.keys (build s lo hi red) == Seq.append (ST.keys red) (Seq.slice s lo (hi + 1)))
          (decreases hi - lo + 1)
  = let size = hi - lo + 1 in
    let kr = ST.keys red in
    if size = 1 then begin
      assert (build s lo hi red == T.Branch red (Seq.index s lo, false) T.Leaf);
      assert (ST.keys (build s lo hi red) == Seq.append kr (Seq.cons (Seq.index s lo) Seq.empty));
      Seq.lemma_eq_intro (ST.keys (build s lo hi red)) (Seq.append kr (Seq.slice s lo (hi + 1)))
    end
    else if size = 2 then begin
      assert (build s lo hi red == T.Branch red (Seq.index s lo, false) (leaf_of (Seq.index s hi) true));
      keys_leaf (Seq.index s hi) true;
      assert (ST.keys (build s lo hi red) == Seq.append kr (Seq.cons (Seq.index s lo) (Seq.create 1 (Seq.index s hi))));
      Seq.lemma_eq_intro (ST.keys (build s lo hi red)) (Seq.append kr (Seq.slice s lo (hi + 1)))
    end
    else if size = 3 then begin
      let l = T.Branch red (Seq.index s lo, false) T.Leaf in
      assert (build s lo hi red == T.Branch l (Seq.index s (lo + 1), false) (leaf_of (Seq.index s hi) false));
      keys_leaf (Seq.index s hi) false;
      assert (ST.keys l == Seq.append kr (Seq.cons (Seq.index s lo) Seq.empty));
      assert (ST.keys (build s lo hi red) == Seq.append (ST.keys l) (Seq.cons (Seq.index s (lo + 1)) (Seq.create 1 (Seq.index s hi))));
      Seq.lemma_eq_intro (ST.keys (build s lo hi red)) (Seq.append kr (Seq.slice s lo (hi + 1)))
    end
    else begin
      let mid = (lo + hi) / 2 in
      keys_build s lo (mid - 1) red;
      let kl = Seq.append kr (Seq.slice s lo mid) in
      let rt = if size % 2 = 0 then build s (mid + 2) hi (leaf_of (Seq.index s (mid + 1)) true)
               else build s (mid + 1) hi T.Leaf in
      let tail = Seq.slice s (mid + 1) (hi + 1) in
      if size % 2 = 0 then begin
        keys_build s (mid + 2) hi (leaf_of (Seq.index s (mid + 1)) true);
        keys_leaf (Seq.index s (mid + 1)) true;
        slice_cons s (mid + 1) (hi + 1);
        Seq.lemma_eq_intro (ST.keys rt) tail
      end else begin
        keys_build s (mid + 1) hi T.Leaf;
        Seq.lemma_eq_intro (ST.keys rt) tail
      end;
      slice_cons s mid (hi + 1);
      slice_split s lo mid (hi + 1);
      Seq.append_assoc kr (Seq.slice s lo mid) (Seq.slice s mid (hi + 1));
      assert (ST.keys (build s lo hi red) == Seq.append kl (Seq.cons (Seq.index s mid) (ST.keys rt)))
    end

let red_arg_facts (#a: Type0) (red: T.tree (a & bool))
  : Lemma (requires red_arg red)
          (ensures ST.rb red /\ ST.black_height red == 0)
  = ()

/// A built tree is red-black but for its root, which is black, and its black height is
/// `bhf` of its size.
let rec rb_build (#a: Type0) (s: Seq.seq a) (lo hi: int) (red: T.tree (a & bool))
  : Lemma (requires 0 <= lo /\ lo <= hi /\ hi < Seq.length s /\ red_arg red)
          (ensures ST.rb (build s lo hi red) /\ not (ST.is_red (build s lo hi red)) /\
                   ST.black_height (build s lo hi red) == bhf (hi - lo + 1) /\
                   T.size (build s lo hi red) == T.size red + (hi - lo + 1))
          (decreases hi - lo + 1)
  = let size = hi - lo + 1 in
    red_arg_facts red;
    assert_norm (bhf 0 == 0);
    assert_norm (bhf 1 == 1);
    assert_norm (bhf 2 == 1);
    assert_norm (bhf 3 == 2);
    if size = 1 then
      assert (build s lo hi red == T.Branch red (Seq.index s lo, false) T.Leaf)
    else if size = 2 then
      assert (build s lo hi red == T.Branch red (Seq.index s lo, false) (leaf_of (Seq.index s hi) true))
    else if size = 3 then begin
      let l = T.Branch red (Seq.index s lo, false) T.Leaf in
      assert (ST.rb l /\ ST.black_height l == 1 /\ not (ST.is_red l));
      assert (build s lo hi red == T.Branch l (Seq.index s (lo + 1), false) (leaf_of (Seq.index s hi) false))
    end
    else begin
      let mid = (lo + hi) / 2 in
      let m = (size - 1) / 2 in
      FStar.Math.Lemmas.euclidean_division_definition (size - 1) 2;
      FStar.Math.Lemmas.euclidean_division_definition size 2;
      FStar.Math.Lemmas.lemma_mod_plus (size - 1) 1 2;
      assert (size % 2 = 0 ==> size == 2 * m + 2);
      assert (size % 2 <> 0 ==> size == 2 * m + 1);
      assert (mid - lo == m);
      assert (bhf size == bhf m + 1);
      rb_build s lo (mid - 1) red;
      let l = build s lo (mid - 1) red in
      if size % 2 = 0 then begin
        let rd = leaf_of (Seq.index s (mid + 1)) true in
        rb_build s (mid + 2) hi rd;
        assert (hi - (mid + 2) + 1 == m);
        assert (build s lo hi red == T.Branch l (Seq.index s mid, false) (build s (mid + 2) hi rd))
      end else begin
        rb_build s (mid + 1) hi T.Leaf;
        assert (hi - (mid + 1) + 1 == m);
        assert (build s lo hi red == T.Branch l (Seq.index s mid, false) (build s (mid + 1) hi T.Leaf))
      end
    end
#pop-options

/// R27.32. The whole of a strictly sorted array is a red-black tree of its elements.
let build_ok (#a: Type0) (s: Seq.seq a) (lo hi: int)
  : Lemma (requires 0 <= lo /\ lo <= hi + 1 /\ hi < Seq.length s)
          (ensures ST.keys (build s lo hi T.Leaf) == Seq.slice s lo (hi + 1) /\
                   ST.red_black (build s lo hi T.Leaf) /\
                   T.size (build s lo hi T.Leaf) == hi - lo + 1)
          [SMTPat (build s lo hi T.Leaf)]
  = if lo <= hi then begin
      keys_build s lo hi T.Leaf;
      rb_build s lo hi T.Leaf;
      Seq.append_empty_l (Seq.slice s lo (hi + 1))
    end
    else Seq.lemma_eq_intro (ST.keys (build #a s lo hi T.Leaf)) (Seq.slice s lo (hi + 1))

(* ------------------------------------------------------------------------------------ *)
(* The heap: building from fresh nodes                                                   *)

/// The boxes an unshared tree reaches are in the heap.
let unshared_boxes_mem (#r: Type0) (left right: r -> B.box r) (h: heap r) (x: B.box r)
  : Lemma (requires RT.unshared left right h x)
          (ensures forall (z: B.box r). L.memP z (RT.boxes (RT.ltree left right h x)) ==> mem h z)
  = RT.unshared_elim left right h x;
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (RT.realizes_mem left right h x (RT.ltree left right h x)))

/// A tree disjoint from what a re-linking touched is as it was, and disjoint from what the
/// re-linking built.
let reshaped_outside (#r: Type0) (left right: r -> B.box r) (h0 h1: heap r) (x y z: B.box r)
  : Lemma (requires RT.reshaped left right h0 h1 x y /\ RT.unshared left right h0 z /\
                    RT.disjoint (RT.boxes (RT.ltree left right h0 z)) (RT.boxes (RT.ltree left right h0 x)))
          (ensures RT.unshared left right h1 z /\ RT.ltree left right h1 z == RT.ltree left right h0 z /\
                   RT.disjoint (RT.boxes (RT.ltree left right h1 y)) (RT.boxes (RT.ltree left right h1 z)))
          [SMTPat (RT.reshaped left right h0 h1 x y); SMTPat (RT.unshared left right h0 z)]
  = RT.framed_outside left right h0 h1 (RT.boxes (RT.ltree left right h0 x)) z;
    unshared_boxes_mem left right h0 z

/// A box outside what a re-linking touched is as it was, and outside what it built.
let reshaped_box (#r: Type0) (left right: r -> B.box r) (h0 h1: heap r) (x y b: B.box r)
  : Lemma (requires RT.reshaped left right h0 h1 x y /\ mem h0 b /\
                    ~ (L.memP b (RT.boxes (RT.ltree left right h0 x))))
          (ensures mem h1 b /\ get h1 b == get h0 b /\
                   ~ (L.memP b (RT.boxes (RT.ltree left right h1 y))))
          [SMTPat (RT.reshaped left right h0 h1 x y); SMTPat (mem h0 b)]
  = ()

/// Re-linking a freshly allocated leaf re-links nothing that was there before it.
let reshaped_fresh_leaf (#r: Type0) (left right: r -> B.box r) (h h2: heap r) (b: B.box r) (v: r) (y: B.box r)
  : Lemma (requires ~ (mem h b) /\ B.is_null b == false /\ B.is_null (left v) /\ B.is_null (right v) /\
                    RT.reshaped left right ((b, v) :: h) h2 b y)
          (ensures RT.reshaped left right h h2 (B.null #r) y)
          [SMTPat (RT.reshaped left right ((b, v) :: h) h2 b y)]
  = RT.alloc_leaf left right h b v;
    RT.ltree_null left right h (B.null #r)

/// Forward forms of `RegionTree`'s allocation and write lemmas, for a body that builds by
/// allocating and linking: each fires on the heap a step leaves and a tree known unshared
/// before it, so what was unshared stays so one step at a time without any later goal
/// naming the intermediate heaps.
let alloc_fwd (#r: Type0) (left right: r -> B.box r) (h: heap r) (b: B.box r) (v: r) (x: B.box r)
  : Lemma (ensures (RT.unshared left right h x /\ ~ (mem h b) ==>
                    RT.unshared left right ((b, v) :: h) x /\
                    RT.ltree left right ((b, v) :: h) x == RT.ltree left right h x /\
                    ~ (L.memP b (RT.boxes (RT.ltree left right h x)))) /\
                   (~ (mem h b) /\ B.is_null b == false /\ B.is_null (left v) /\ B.is_null (right v) ==>
                    RT.unshared left right ((b, v) :: h) b /\
                    RT.ltree left right ((b, v) :: h) b == T.Branch T.Leaf (b, v) T.Leaf))
          [SMTPat ((b, v) :: h); SMTPat (RT.unshared left right h x)]
  = FStar.Classical.move_requires (RT.alloc_outside left right h x b) v;
    FStar.Classical.move_requires (RT.alloc_leaf left right h b) v

let upd_fwd (#r: Type0) (left right: r -> B.box r) (h: heap r) (b: B.box r) (v: r) (x: B.box r)
  : Lemma (ensures (RT.unshared left right h x /\ ~ (L.memP b (RT.boxes (RT.ltree left right h x))) ==>
                    RT.unshared left right (upd h b v) x /\
                    RT.ltree left right (upd h b v) x == RT.ltree left right h x) /\
                   (mem h b /\ B.is_null b == false /\
                    RT.unshared left right h (left v) /\ RT.unshared left right h (right v) /\
                    ~ (L.memP b (RT.boxes (RT.ltree left right h (left v)))) /\
                    ~ (L.memP b (RT.boxes (RT.ltree left right h (right v)))) /\
                    RT.disjoint (RT.boxes (RT.ltree left right h (left v))) (RT.boxes (RT.ltree left right h (right v))) ==>
                    RT.unshared left right (upd h b v) b /\
                    RT.ltree left right (upd h b v) b ==
                      T.Branch (RT.ltree left right h (left v)) (b, v) (RT.ltree left right h (right v))))
          [SMTPat (upd h b v); SMTPat (RT.unshared left right h x)]
  = FStar.Classical.move_requires (RT.upd_outside left right h x b) v;
    FStar.Classical.move_requires (RT.upd_node left right h b) v

/// The tree a node just written over two unshared, disjoint subtrees reaches, in terms of
/// its children's trees before the write (the heap the callee contracts speak of).
let tree_upd_node (#r #t: Type0) (view: B.box r -> r -> t) (left right: r -> B.box r)
    (h: heap r) (b: B.box r) (v: r)
  : Lemma (ensures (mem h b /\ B.is_null b == false /\
                    RT.unshared left right h (left v) /\ RT.unshared left right h (right v) /\
                    ~ (L.memP b (RT.boxes (RT.ltree left right h (left v)))) /\
                    ~ (L.memP b (RT.boxes (RT.ltree left right h (right v)))) /\
                    RT.disjoint (RT.boxes (RT.ltree left right h (left v))) (RT.boxes (RT.ltree left right h (right v))) ==>
                    tree_of view left right (upd h b v) b ==
                      T.Branch (tree_of view left right h (left v)) (view b v) (tree_of view left right h (right v))))
          [SMTPat (tree_of view left right (upd h b v) b)]
  = FStar.Classical.move_requires (RT.upd_node left right h b) v;
    RT.tree_of_vmap view left right (upd h b v) b;
    RT.tree_of_vmap view left right h (left v);
    RT.tree_of_vmap view left right h (right v)

/// A write to the left child of an unshared node that keeps the child the root of an
/// unshared tree disjoint from the node and its other child keeps the node unshared, over
/// the child's new tree.
let upd_left_child (#r: Type0) (left right: r -> B.box r) (h: heap r) (x b: B.box r) (v: r)
  : Lemma (requires RT.unshared left right h x /\ mem h x /\ B.is_null x == false /\
                    b == left (get h x) /\ mem h b /\ B.is_null b == false /\
                    RT.unshared left right h (left v) /\ RT.unshared left right h (right v) /\
                    ~ (L.memP b (RT.boxes (RT.ltree left right h (left v)))) /\
                    ~ (L.memP b (RT.boxes (RT.ltree left right h (right v)))) /\
                    ~ (L.memP x (RT.boxes (RT.ltree left right h (left v)))) /\
                    ~ (L.memP x (RT.boxes (RT.ltree left right h (right v)))) /\
                    RT.disjoint (RT.boxes (RT.ltree left right h (left v))) (RT.boxes (RT.ltree left right h (right v))) /\
                    RT.disjoint (RT.boxes (RT.ltree left right h (left v))) (RT.boxes (RT.ltree left right h (right (get h x)))) /\
                    RT.disjoint (RT.boxes (RT.ltree left right h (right v))) (RT.boxes (RT.ltree left right h (right (get h x)))))
          (ensures RT.unshared left right (upd h b v) x /\
                   RT.ltree left right (upd h b v) x ==
                     T.Branch (T.Branch (RT.ltree left right h (left v)) (b, v) (RT.ltree left right h (right v)))
                              (x, get h x) (RT.ltree left right h (right (get h x))))
          [SMTPat (RT.unshared left right h x); SMTPat (upd h b v)]
  = let rx = get h x in
    let s = right rx in
    RT.unshared_step left right h x;
    RT.unshared_step left right h b;
    let h' = upd h b v in
    RT.upd_node left right h b v;
    RT.upd_outside left right h s b v;
    unshared_boxes_mem left right h s;
    RT.upd_node left right h' x rx;
    upd_same h' x

/// The default case of `ConstructRootFromSortedArray`: `root`, already linked to its left
/// subtree in `h3`, gets as right child the root `y` of a tree built entirely of boxes new
/// since `h3` (`reshaped h3 h5 null y`, with `reshaped_fresh_leaf` folding in a saved red
/// node allocated just before). The node is then the root of the two subtrees, and of a
/// re-linking of `red` since `h0`.
let link_right_core (#r #t: Type0) (view: B.box r -> r -> t) (left right: r -> B.box r)
    (h0 h3 h5: heap r) (red root y: B.box r) (v: r)
  : Lemma (requires RT.reshaped left right h0 h3 red root /\ RT.unshared left right h3 root /\
                    mem h3 root /\ B.is_null root == false /\ B.is_null (right (get h3 root)) /\
                    RT.reshaped left right h3 h5 (B.null #r) y /\ RT.unshared left right h5 y /\
                    left v == left (get h3 root) /\ right v == y)
          (ensures RT.unshared left right (upd h5 root v) root /\
                   tree_of view left right (upd h5 root v) root ==
                     T.Branch (tree_of view left right h3 (left v)) (view root v) (tree_of view left right h5 y) /\
                   tree_of view left right (upd h5 root v) (left v) == tree_of view left right h3 (left v) /\
                   tree_of view left right (upd h5 root v) y == tree_of view left right h5 y /\
                   RT.reshaped left right h0 (upd h5 root v) red root)
  = let rv = get h3 root in
    let l = left rv in
    RT.ltree_null left right h3 (B.null #r);
    RT.unshared_step left right h3 root;
    unshared_boxes_mem left right h3 root;
    unshared_boxes_mem left right h5 y;
    RT.framed_outside left right h3 h5 [] root;
    RT.unshared_step left right h5 root;
    let ly = RT.ltree left right h5 y in
    let ll = RT.ltree left right h5 l in
    let fresh_y (z: B.box r) : Lemma (L.memP z (RT.boxes ly) ==> ~ (mem h3 z)) = () in
    FStar.Classical.forall_intro fresh_y;
    let in_root (z: B.box r) : Lemma (L.memP z (RT.boxes ll) ==> L.memP z (RT.boxes (RT.ltree left right h3 root))) =
      L.append_memP (RT.boxes ll) (RT.boxes (RT.ltree left right h3 (right rv))) z in
    FStar.Classical.forall_intro in_root;
    RT.upd_node left right h5 root v;
    RT.upd_outside left right h5 l root v;
    RT.upd_outside left right h5 y root v;
    RT.tree_of_vmap view left right (upd h5 root v) l;
    RT.tree_of_vmap view left right (upd h5 root v) y;
    RT.tree_of_vmap view left right (upd h5 root v) root;
    RT.tree_of_vmap view left right h3 l;
    RT.tree_of_vmap view left right h5 l;
    RT.tree_of_vmap view left right h5 y;
    let h6 = upd h5 root v in
    let fr (z: B.box r) : Lemma (mem h5 z ==> mem h6 z /\ (z =!= root ==> lookup h6 z == lookup h5 z)) =
      lookup_upd h5 root z v in
    FStar.Classical.forall_intro fr;
    let wi (z: B.box r) : Lemma (L.memP z (RT.boxes (RT.ltree left right h6 root)) ==>
                                 L.memP z (RT.boxes (RT.ltree left right h0 red)) \/ ~ (mem h0 z)) =
      L.append_memP (RT.boxes ll) (RT.boxes ly) z in
    FStar.Classical.forall_intro wi

/// `link_right_core` for every heap and right child the rest of the method may produce,
/// stated at `h3`, which a ghost snapshot can name, so that a ghost call before the
/// conditional covers both of its arms.
let link_right (#r #t: Type0) (view: B.box r -> r -> t) (left right: r -> B.box r)
    (h0 h3: heap r) (red root: B.box r)
  : Lemma (requires RT.reshaped left right h0 h3 red root /\ RT.unshared left right h3 root /\
                    mem h3 root /\ B.is_null root == false /\ B.is_null (right (get h3 root)))
          (ensures (forall (h5: heap r) (y: B.box r) (v: r).
                     {:pattern RT.reshaped left right h3 h5 (B.null #r) y; upd h5 root v}
                     RT.reshaped left right h3 h5 (B.null #r) y /\ RT.unshared left right h5 y /\
                     left v == left (get h3 root) /\ right v == y ==>
                     RT.unshared left right (upd h5 root v) root /\
                     tree_of view left right (upd h5 root v) root ==
                       T.Branch (tree_of view left right h3 (left v)) (view root v) (tree_of view left right h5 y) /\
                     tree_of view left right (upd h5 root v) (left v) == tree_of view left right h3 (left v) /\
                     tree_of view left right (upd h5 root v) y == tree_of view left right h5 y /\
                     RT.reshaped left right h0 (upd h5 root v) red root) /\
                   (forall (h5: heap r) (y: B.box r).
                     {:pattern RT.reshaped left right h3 h5 (B.null #r) y}
                     RT.reshaped left right h3 h5 (B.null #r) y ==> mem h5 root /\ get h5 root == get h3 root))
  = let aux (h5: heap r) (y: B.box r) (v: r)
      : Lemma (RT.reshaped left right h3 h5 (B.null #r) y /\ RT.unshared left right h5 y /\
               left v == left (get h3 root) /\ right v == y ==>
               RT.unshared left right (upd h5 root v) root /\
               tree_of view left right (upd h5 root v) root ==
                 T.Branch (tree_of view left right h3 (left v)) (view root v) (tree_of view left right h5 y) /\
               tree_of view left right (upd h5 root v) (left v) == tree_of view left right h3 (left v) /\
               tree_of view left right (upd h5 root v) y == tree_of view left right h5 y /\
               RT.reshaped left right h0 (upd h5 root v) red root)
      = FStar.Classical.move_requires (link_right_core view left right h0 h3 h5 red root y) v in
    FStar.Classical.forall_intro_3 aux

/// One step of `build` past the base cases, at the midpoint `mid` and the parity `even` the
/// caller computed. It takes a region's projections only to be callable as a `[RegionOp]`
/// lemma; it says nothing about any heap.
let build_split (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (s: Seq.seq t) (lo hi mid: int) (even: bool) (red: T.tree (t & bool))
  : Lemma (requires 0 <= lo /\ hi < Seq.length s /\ hi - lo + 1 >= 4 /\
                    2 * mid <= lo + hi /\ lo + hi <= 2 * mid + 1 /\ even == ((hi - lo + 1) % 2 = 0))
          (ensures build s lo hi red ==
                     T.Branch (build s lo (mid - 1) red) (Seq.index s mid, false)
                              (if even
                               then build s (mid + 2) hi (T.Branch T.Leaf (Seq.index s (mid + 1), true) T.Leaf)
                               else build s (mid + 1) hi T.Leaf))
  = assert (mid == (lo + hi) / 2)

/// The tree a freshly allocated node with no children reaches.
let tree_alloc_leaf (#r #t: Type0) (view: B.box r -> r -> t) (left right: r -> B.box r)
    (h: heap r) (b: B.box r) (v: r)
  : Lemma (ensures (~ (mem h b) /\ B.is_null b == false /\ B.is_null (left v) /\ B.is_null (right v) ==>
                    tree_of view left right ((b, v) :: h) b == T.Branch T.Leaf (view b v) T.Leaf))
          [SMTPat (tree_of view left right ((b, v) :: h) b)]
  = FStar.Classical.move_requires (RT.alloc_leaf left right h b) v;
    RT.tree_of_vmap view left right ((b, v) :: h) b

/// `size % 2` as the code computes it, on the non-negative `size` the method takes, is the
/// parity its specification names.
let rem2 (a: FStar.Int32.t)
  : Lemma (requires FStar.Int32.v a >= 0)
          (ensures FStar.Int32.v (FStar.Int32.rem a 2l) == FStar.Int32.v a % 2)
          [SMTPat (FStar.Int32.rem a 2l)]
  = ()
