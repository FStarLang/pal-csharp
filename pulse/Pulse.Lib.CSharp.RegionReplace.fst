module Pulse.Lib.CSharp.RegionReplace

/// R32.10. A write to one node of the tree a pointer reaches that keeps the node's links: the
/// tree keeps its shape and its boxes, and its in-order keys change at the node's position
/// only. This is what an in-place value replacement (`node.Item = ...` on a node a search
/// found) does to a region's tree.
///
/// Nothing here is trusted beyond `Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8).

open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module S = Pulse.Lib.CSharp.Sorted
module O = Pulse.Lib.CSharp.Order
module Seq = FStar.Seq

/// `x` is one of the nodes of the tree `root` reaches: what `SpecRegion.InTree` is.
let in_tree (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a) (h: heap a)
    (root x: B.box a) : prop =
  L.memP x (boxes (ltree left right h root))

/// The boxed tree with the payload at `x` replaced by `v`.
let rec set_at (#a: Type0) (x: B.box a) (v: a) (t: T.tree (B.box a & a))
  : Tot (T.tree (B.box a & a)) (decreases t)
  = match t with
    | T.Leaf -> T.Leaf
    | T.Branch l (b, w) rr -> T.Branch (set_at x v l) (b, (if eq_box b x then v else w)) (set_at x v rr)

let rec set_at_outside (#a: Type0) (x: B.box a) (v: a) (t: T.tree (B.box a & a))
  : Lemma (requires ~ (L.memP x (boxes t))) (ensures set_at x v t == t) (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ rr -> set_at_outside x v l; set_at_outside x v rr

let rec boxes_set_at (#a: Type0) (x: B.box a) (v: a) (t: T.tree (B.box a & a))
  : Lemma (ensures boxes (set_at x v t) == boxes t) (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ rr -> boxes_set_at x v l; boxes_set_at x v rr

/// A write keeping `x`'s links makes the heap realize the tree with `x`'s payload replaced.
let rec realizes_set_at (#a: Type0) (left right: a -> B.box a) (h: heap a) (y: B.box a)
    (t: T.tree (B.box a & a)) (x: B.box a) (v: a)
  : Lemma (requires realizes left right h y t /\ distinct (boxes t) /\ mem h x /\
                    left v == left (get h x) /\ right v == right (get h x))
          (ensures realizes left right (upd h x v) y (set_at x v t))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (b, w) rr ->
      if eq_box b x then begin
        set_at_outside x v l; set_at_outside x v rr;
        realizes_upd left right h (left w) l x v;
        realizes_upd left right h (right w) rr x v
      end else begin
        realizes_set_at left right h (left w) l x v;
        realizes_set_at left right h (right w) rr x v
      end

/// The position of `x` in the in-order sequence of the tree's nodes, or -1.
let rec pos (#a: Type0) (x: B.box a) (t: T.tree (B.box a & a)) : GTot int (decreases t) =
  match t with
  | T.Leaf -> -1
  | T.Branch l (b, _) rr ->
    if eq_box b x then T.size l
    else if FStar.IndefiniteDescription.strong_excluded_middle (L.memP x (boxes l)) then pos x l
    else if FStar.IndefiniteDescription.strong_excluded_middle (L.memP x (boxes rr)) then T.size l + 1 + pos x rr
    else -1

let rec size_vmap (#a #v: Type0) (view: B.box a -> a -> v) (t: T.tree (B.box a & a))
  : Lemma (ensures T.size (vmap view t) == T.size t) (decreases t)
          [SMTPat (T.size (vmap view t))]
  = match t with T.Leaf -> () | T.Branch l _ rr -> size_vmap view l; size_vmap view rr

let append_upd_left (#k: Type) (s1 s2: Seq.seq k) (i: nat{i < Seq.length s1}) (v: k)
  : Lemma (Seq.append (Seq.upd s1 i v) s2 == Seq.upd (Seq.append s1 s2) i v)
  = Seq.lemma_eq_intro (Seq.append (Seq.upd s1 i v) s2) (Seq.upd (Seq.append s1 s2) i v)

let append_upd_right (#k: Type) (s1 s2: Seq.seq k) (i: nat{i < Seq.length s2}) (v: k)
  : Lemma (Seq.append s1 (Seq.upd s2 i v) == Seq.upd (Seq.append s1 s2) (Seq.length s1 + i) v)
  = Seq.lemma_eq_intro (Seq.append s1 (Seq.upd s2 i v)) (Seq.upd (Seq.append s1 s2) (Seq.length s1 + i) v)

let cons_upd (#k: Type) (u: k) (s: Seq.seq k) (i: nat{i < Seq.length s}) (v: k)
  : Lemma (Seq.cons u (Seq.upd s i v) == Seq.upd (Seq.cons u s) (i + 1) v)
  = Seq.lemma_eq_intro (Seq.cons u (Seq.upd s i v)) (Seq.upd (Seq.cons u s) (i + 1) v)

/// The in-order keys of the replaced tree: the old ones, with the key at `x`'s position
/// replaced; what was there is `x`'s old key.
let rec keys_set_at (#a #k #g: Type0) (view: B.box a -> a -> (k & g)) (left right: a -> B.box a)
    (h: heap a) (y: B.box a) (t: T.tree (B.box a & a)) (x: B.box a) (v: a)
  : Lemma (requires realizes left right h y t /\ distinct (boxes t) /\ L.memP x (boxes t))
          (ensures mem h x /\
                   (let j = pos x t in
                    let s0 = ST.keys (vmap view t) in
                    0 <= j /\ j < Seq.length s0 /\
                    Seq.index s0 j == fst (view x (get h x)) /\
                    ST.keys (vmap view (set_at x v t)) == Seq.upd s0 j (fst (view x v))))
          (decreases t)
  = match t with
    | T.Branch l (b, w) rr ->
      let sl = ST.keys (vmap view l) in
      let sr = ST.keys (vmap view rr) in
      if eq_box b x then begin
        set_at_outside x v l; set_at_outside x v rr;
        Seq.lemma_eq_intro (Seq.append sl (Seq.cons (fst (view x v)) sr))
                           (Seq.upd (Seq.append sl (Seq.cons (fst (view b w)) sr)) (Seq.length sl) (fst (view x v)))
      end else if FStar.IndefiniteDescription.strong_excluded_middle (L.memP x (boxes l)) then begin
        keys_set_at view left right h (left w) l x v;
        set_at_outside x v rr;
        append_upd_left sl (Seq.cons (fst (view b w)) sr) (pos x l) (fst (view x v))
      end else begin
        keys_set_at view left right h (right w) rr x v;
        set_at_outside x v l;
        cons_upd (fst (view b w)) sr (pos x rr) (fst (view x v));
        append_upd_right sl (Seq.cons (fst (view b w)) sr) (pos x rr + 1) (fst (view x v))
      end

/// Two trees of the same shape, with the same tags (colours) at every node.
let rec same_shape (#k #g: Type0) (t1 t2: T.tree (k & g)) : Tot prop (decreases t1) =
  match t1, t2 with
  | T.Leaf, T.Leaf -> True
  | T.Branch l1 (_, g1) r1, T.Branch l2 (_, g2) r2 -> g1 == g2 /\ same_shape l1 l2 /\ same_shape r1 r2
  | _ -> False

let rec same_shape_rb (#k: Type0) (t1 t2: T.tree (k & bool))
  : Lemma (requires same_shape t1 t2)
          (ensures ST.rb t1 == ST.rb t2 /\ ST.is_red t1 == ST.is_red t2 /\
                   ST.black_height t1 == ST.black_height t2 /\ T.size t1 == T.size t2)
          (decreases t1)
  = match t1, t2 with
    | T.Leaf, T.Leaf -> ()
    | T.Branch l1 _ r1, T.Branch l2 _ r2 -> same_shape_rb l1 l2; same_shape_rb r1 r2

let rec shape_set_at (#a #k #g: Type0) (view: B.box a -> a -> (k & g)) (left right: a -> B.box a)
    (h: heap a) (y: B.box a) (t: T.tree (B.box a & a)) (x: B.box a) (v: a)
  : Lemma (requires realizes left right h y t /\ mem h x /\ snd (view x v) == snd (view x (get h x)))
          (ensures same_shape (vmap view (set_at x v t)) (vmap view t))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (b, w) rr ->
      shape_set_at view left right h (left w) l x v;
      shape_set_at view left right h (right w) rr x v

/// R32.10. A write to a node `x` of the unshared tree `root` reaches that keeps `x`'s links:
/// the tree stays unshared, its keys change at `x`'s position only, and, if the write keeps
/// `x`'s tag (colour), its shape, size and colouring are unchanged.
let write_in_tree (#a #k: Type0) (view: B.box a -> a -> (k & bool)) (left right: a -> B.box a)
    (h: heap a) (root x: B.box a) (v: a)
  : Lemma (requires unshared left right h root /\ in_tree view left right h root x /\
                    (mem h x ==> left v == left (get h x) /\ right v == right (get h x)))
          (ensures mem h x /\ unshared left right (upd h x v) root /\
                   (let t0 = tree_of view left right h root in
                    let t1 = tree_of view left right (upd h x v) root in
                    let j = pos x (ltree left right h root) in
                    0 <= j /\ j < Seq.length (ST.keys t0) /\
                    Seq.index (ST.keys t0) j == fst (view x (get h x)) /\
                    ST.keys t1 == Seq.upd (ST.keys t0) j (fst (view x v)) /\
                    (snd (view x v) == snd (view x (get h x)) ==>
                       ST.red_black t1 == ST.red_black t0 /\ T.size t1 == T.size t0)))
          [SMTPat (tree_of view left right (upd h x v) root); SMTPat (unshared left right h root)]
  = let t = ltree left right h root in
    unshared_elim left right h root;
    realizes_mem left right h root t x;
    keys_set_at view left right h root t x v;
    realizes_set_at left right h root t x v;
    boxes_set_at x v t;
    unshared_intro left right (upd h x v) root (set_at x v t);
    tree_of_vmap view left right h root;
    tree_of_vmap view left right (upd h x v) root;
    if FStar.IndefiniteDescription.strong_excluded_middle (snd (view x v) == snd (view x (get h x)))
    then begin
      shape_set_at view left right h root t x v;
      same_shape_rb (vmap view (set_at x v t)) (vmap view t)
    end

/// The same write, for the unshared-ness alone (no view to name).
let write_unshared (#a: Type0) (left right: a -> B.box a) (h: heap a) (root x: B.box a) (v: a)
  : Lemma (requires unshared left right h root /\ L.memP x (boxes (ltree left right h root)) /\
                    (mem h x ==> left v == left (get h x) /\ right v == right (get h x)))
          (ensures unshared left right (upd h x v) root)
          [SMTPat (unshared left right (upd h x v) root); SMTPat (unshared left right h root)]
  = let t = ltree left right h root in
    unshared_elim left right h root;
    realizes_mem left right h root t x;
    realizes_set_at left right h root t x v;
    boxes_set_at x v t;
    unshared_intro left right (upd h x v) root (set_at x v t)

/// R32.10. A key replaced by one that compares as it does keeps a strictly sorted sequence
/// strictly sorted, at the same positions.
let upd_equiv (#t: Type) (c: O.comparer t) (s: Seq.seq t) (j: nat) (k1: t)
  : Lemma (requires S.strictly_sorted c s /\ j < Seq.length s /\
                    (forall (z: t). O.compare c k1 z == O.compare c (Seq.index s j) z))
          (ensures S.strictly_sorted c (Seq.upd s j k1))
          [SMTPat (S.strictly_sorted c (Seq.upd s j k1))]
  = let s1 = Seq.upd s j k1 in
    let aux (i0 i1: nat)
      : Lemma (i0 < i1 /\ i1 < Seq.length s1 ==> O.compare c (Seq.index s1 i0) (Seq.index s1 i1) < 0) =
      if i0 < i1 && i1 < Seq.length s1 then begin
        O.compare_antisym c (Seq.index s i0) k1;
        O.compare_antisym c (Seq.index s i0) (Seq.index s j);
        O.compare_antisym c k1 (Seq.index s i0);
        O.compare_antisym c (Seq.index s j) (Seq.index s i0)
      end in
    FStar.Classical.forall_intro_2 aux

/// In a strictly sorted sequence, an element's key index is its position.
let key_index_at (#t: Type) (c: O.comparer t) (s: Seq.seq t) (i j: nat)
  : Lemma (requires S.strictly_sorted c s /\ i < Seq.length s /\ j < Seq.length s /\
                    O.compare c (Seq.index s i) (Seq.index s j) == 0)
          (ensures i == j)
  = if i < j then () else if j < i then O.compare_antisym c (Seq.index s i) (Seq.index s j) else ()

let rec realizes_child (#a: Type0) (left right: a -> B.box a) (h: heap a) (y: B.box a)
    (t: T.tree (B.box a & a)) (x: B.box a)
  : Lemma (requires realizes left right h y t /\ L.memP x (boxes t))
          (ensures mem h x /\
                   (B.is_null (left (get h x)) == false ==> L.memP (left (get h x)) (boxes t)) /\
                   (B.is_null (right (get h x)) == false ==> L.memP (right (get h x)) (boxes t)))
          (decreases t)
  = match t with
    | T.Branch l (b, w) rr ->
      if eq_box b x then begin
        (match l with T.Leaf -> () | T.Branch _ _ _ -> ());
        (match rr with T.Leaf -> () | T.Branch _ _ _ -> ())
      end
      else if FStar.IndefiniteDescription.strong_excluded_middle (L.memP x (boxes l))
      then realizes_child left right h (left w) l x
      else realizes_child left right h (right w) rr x

/// The children of a node of the tree are nodes of the tree: a search that starts at the
/// root stays in it.
let in_tree_child (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a) (h: heap a)
    (root x: B.box a)
  : Lemma (requires unshared left right h root /\ in_tree view left right h root x)
          (ensures mem h x /\
                   (B.is_null (left (get h x)) == false ==> in_tree view left right h root (left (get h x))) /\
                   (B.is_null (right (get h x)) == false ==> in_tree view left right h root (right (get h x))))
          [SMTPat (in_tree view left right h root x); SMTPat (get h x)]
  = unshared_elim left right h root;
    realizes_child left right h root (ltree left right h root) x

/// The root of a non-empty tree is a node of it.
let in_tree_root (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a) (h: heap a)
    (root: B.box a)
  : Lemma (requires unshared left right h root /\ B.is_null root == false)
          (ensures in_tree view left right h root root)
          [SMTPat (in_tree view left right h root root)]
  = unshared_mem left right h root;
    unshared_step left right h root

/// In a strictly sorted sequence, an element's key index is its position: two positions
/// holding the same element are one.
let key_index_index (#t: Type0) (c: O.comparer t) (s: Seq.seq t) (i: nat)
  : Lemma (requires S.strictly_sorted c s /\ i < Seq.length s)
          (ensures S.key_index c s (Seq.index s i) == i)
          [SMTPat (S.strictly_sorted c s); SMTPat (Seq.index s i)]
  = let x = Seq.index s i in
    let s1 = Seq.slice s 0 i in
    let s2 = Seq.slice s i (Seq.length s) in
    Seq.lemma_split s i;
    ST.lower_bound_all_below c s1 x;
    ST.lower_bound_all_above c s2 x;
    ST.lower_bound_append c s1 s2 x
