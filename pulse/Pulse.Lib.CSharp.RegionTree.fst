module Pulse.Lib.CSharp.RegionTree

/// R27.16. The shape theory a region needs once its objects are *written*: a heap pointer
/// that reaches a tree of distinct boxes (`unshared`), the tree of boxes and records it
/// reaches (`ltree`), and what one write or one allocation does to it. The lemmas are
/// stated over `ltree` and fire on the heap a write leaves, so a body that rewires nodes is
/// verified by the solver chaining one write at a time.
///
/// Nothing here is trusted: it is built on `Pulse.Lib.CSharp.Region`, whose only trusted
/// fact is `RefEq.ref_eq` (R27.8).

open Pulse.Lib.CSharp.Region
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree

(* ------------------------------------------------------------------------------------ *)
(* Boxed trees                                                                           *)

/// The tree `x` reaches, each node the box it is with the record it holds.
let rec ltree_n (#a: Type0) (left right: a -> B.box a) (n: nat) (h: heap a) (x: B.box a)
  : GTot (T.tree (B.box a & a)) (decreases n)
  = if n = 0 || B.is_null x then T.Leaf
    else match lookup h x with
      | None -> T.Leaf
      | Some r -> T.Branch (ltree_n left right (n - 1) h (left r)) (x, r)
                           (ltree_n left right (n - 1) h (right r))

[@@"opaque_to_smt"]
let ltree (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : GTot (T.tree (B.box a & a))
  = ltree_n left right (fuel h) h x

/// The boxes of a boxed tree, root first.
let rec boxes (#a: Type0) (t: T.tree (B.box a & a)) : Tot (list (B.box a)) (decreases t) =
  match t with
  | T.Leaf -> []
  | T.Branch l (b, _) r -> b :: L.append (boxes l) (boxes r)

let rec distinct (#a: Type) (l: list a) : prop =
  match l with
  | [] -> True
  | x :: t -> ~ (L.memP x t) /\ distinct t

let disjoint (#a: Type) (l1 l2: list a) : prop =
  forall (y: a). L.memP y l1 ==> ~ (L.memP y l2)

/// The view of every node.
let rec vmap (#a #v: Type0) (view: B.box a -> a -> v) (t: T.tree (B.box a & a))
  : Tot (T.tree v) (decreases t)
  = match t with
    | T.Leaf -> T.Leaf
    | T.Branch l (b, r) rr -> T.Branch (vmap view l) (view b r) (vmap view rr)

let vmap_branch (#a #v: Type0) (view: B.box a -> a -> v) (l: T.tree (B.box a & a)) (b: B.box a)
    (r: a) (rr: T.tree (B.box a & a))
  : Lemma (ensures vmap view (T.Branch l (b, r) rr) == T.Branch (vmap view l) (view b r) (vmap view rr))
          [SMTPat (vmap view (T.Branch l (b, r) rr))]
  = ()

let vmap_leaf (#a #v: Type0) (view: B.box a -> a -> v)
  : Lemma (ensures vmap view (T.Leaf #(B.box a & a)) == T.Leaf) [SMTPat (vmap view (T.Leaf #(B.box a & a)))]
  = ()

/// `x` reaches exactly `t` in `h`; no fuel, so it composes.
let rec realizes (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
    (t: T.tree (B.box a & a)) : Tot prop (decreases t)
  = match t with
    | T.Leaf -> B.is_null x == true
    | T.Branch l (b, r) rr ->
      x == b /\ B.is_null x == false /\ lookup h x == Some r /\
      realizes left right h (left r) l /\ realizes left right h (right r) rr

/// R27.16. A pointer of a region that reaches a tree in which no box occurs twice: what
/// lets a write to one node leave every other node's subtree alone.
[@@"opaque_to_smt"]
let unshared (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a) : prop =
  wf left right h x /\ distinct (boxes (ltree left right h x))

(* ------------------------------------------------------------------------------------ *)
(* Lists                                                                                 *)

let rec mem_append (#a: Type) (y: a) (l1 l2: list a)
  : Lemma (ensures L.memP y (L.append l1 l2) <==> L.memP y l1 \/ L.memP y l2)
          [SMTPat (L.memP y (L.append l1 l2))]
  = match l1 with [] -> () | _ :: t -> mem_append y t l2

let rec distinct_append (#a: Type) (l1 l2: list a)
  : Lemma (ensures distinct (L.append l1 l2) <==> distinct l1 /\ distinct l2 /\ disjoint l1 l2)
          [SMTPat (distinct (L.append l1 l2))]
  = match l1 with [] -> () | _ :: t -> distinct_append t l2

let mem_boxes_branch (#a: Type0) (y: B.box a) (l: T.tree (B.box a & a)) (b: B.box a) (r: a)
    (rr: T.tree (B.box a & a))
  : Lemma (ensures L.memP y (boxes (T.Branch l (b, r) rr)) <==>
                   y == b \/ L.memP y (boxes l) \/ L.memP y (boxes rr))
          [SMTPat (L.memP y (boxes (T.Branch l (b, r) rr)))]
  = ()

let rec rem (#a: Type0) (y: B.box a) (d: list (B.box a)) : Tot (list (B.box a)) (decreases d) =
  match d with
  | [] -> []
  | z :: t -> if eq_box z y then t else z :: rem y t

let rec rem_length (#a: Type0) (y: B.box a) (d: list (B.box a))
  : Lemma (requires L.memP y d) (ensures L.length (rem y d) == L.length d - 1)
  = match d with
    | z :: t -> if eq_box z y then () else rem_length y t

let rec rem_mem (#a: Type0) (y z: B.box a) (d: list (B.box a))
  : Lemma (requires L.memP z d /\ ~ (z == y)) (ensures L.memP z (rem y d))
  = match d with
    | w :: t -> if eq_box w y then () else if eq_box w z then () else rem_mem y z t

/// Pigeonhole: distinct boxes, all drawn from `d`, are at most as many as `d`.
let rec distinct_length (#a: Type0) (l d: list (B.box a))
  : Lemma (requires distinct l /\ (forall y. L.memP y l ==> L.memP y d))
          (ensures L.length l <= L.length d)
          (decreases l)
  = match l with
    | [] -> ()
    | y :: t ->
      let d' = rem y d in
      rem_length y d;
      let aux (z: B.box a) : Lemma (L.memP z t ==> L.memP z d') =
        if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z t)
        then rem_mem y z d else () in
      FStar.Classical.forall_intro aux;
      distinct_length t d'

let rec mem_dom (#a: Type0) (h: heap a) (y: B.box a)
  : Lemma (requires mem h y) (ensures L.memP y (L.map fst h))
  = match h with
    | (b, _) :: t -> if eq_box b y then () else mem_dom t y

(* ------------------------------------------------------------------------------------ *)
(* Realizing a tree                                                                      *)

let rec boxes_length (#a: Type0) (t: T.tree (B.box a & a))
  : Lemma (ensures L.length (boxes t) == T.size t /\ T.height t <= T.size t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ r -> boxes_length l; boxes_length r; L.append_length (boxes l) (boxes r)

let rec realizes_mem (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
    (t: T.tree (B.box a & a)) (y: B.box a)
  : Lemma (requires realizes left right h x t /\ L.memP y (boxes t)) (ensures mem h y)
          (decreases t)
  = match t with
    | T.Branch l (b, r) rr ->
      if L.memP y (boxes l) then realizes_mem left right h (left r) l y
      else if L.memP y (boxes rr) then realizes_mem left right h (right r) rr y
      else ()

let rec realizes_closed (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (n: nat) (h: heap a) (x: B.box a) (t: T.tree (B.box a & a))
  : Lemma (requires realizes left right h x t /\ T.height t <= n)
          (ensures closed left right n h x /\ ltree_n left right n h x == t /\
                   tree_n view left right n h x == vmap view t)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (b, r) rr ->
      realizes_closed view left right (n - 1) h (left r) l;
      realizes_closed view left right (n - 1) h (right r) rr

let rec closed_realizes (#a: Type0) (left right: a -> B.box a) (n: nat) (h: heap a) (x: B.box a)
  : Lemma (requires closed left right n h x)
          (ensures realizes left right h x (ltree_n left right n h x))
          (decreases n)
  = if B.is_null x then ()
    else (closed_realizes left right (n - 1) h (left (get h x));
          closed_realizes left right (n - 1) h (right (get h x)))

let rec tree_n_vmap (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (n: nat) (h: heap a) (x: B.box a)
  : Lemma (ensures tree_n view left right n h x == vmap view (ltree_n left right n h x))
          (decreases n)
  = if n = 0 || B.is_null x then ()
    else match lookup h x with
      | None -> ()
      | Some r -> tree_n_vmap view left right (n - 1) h (left r);
                 tree_n_vmap view left right (n - 1) h (right r)

/// The view tree is the boxed tree seen through `view`, at any heap.
let tree_of_vmap (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h: heap a) (x: B.box a)
  : Lemma (ensures tree_of view left right h x == vmap view (ltree left right h x))
          [SMTPat (tree_of view left right h x)]
  = reveal_opaque (`%tree_of) (tree_of #a #v); reveal_opaque (`%unshared) (unshared #a); reveal_opaque (`%ltree) (ltree #a); reveal_opaque (`%wf) (wf #a);
    tree_n_vmap view left right (fuel h) h x

/// A distinct tree a heap realizes is the whole of what the pointer reaches.
let unshared_intro (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
    (t: T.tree (B.box a & a))
  : Lemma (requires realizes left right h x t /\ distinct (boxes t))
          (ensures unshared left right h x /\ ltree left right h x == t)
  = reveal_opaque (`%unshared) (unshared #a); reveal_opaque (`%ltree) (ltree #a); reveal_opaque (`%wf) (wf #a);
    let aux (y: B.box a) : Lemma (L.memP y (boxes t) ==> L.memP y (L.map fst h)) =
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (boxes t))
      then (realizes_mem left right h x t y; mem_dom h y) else () in
    FStar.Classical.forall_intro aux;
    distinct_length (boxes t) (L.map fst h);
    FStar.List.Tot.Properties.map_lemma fst h;
    boxes_length t;
    realizes_closed #a #unit (fun _ _ -> ()) left right (fuel h) h x t

let unshared_elim (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires unshared left right h x)
          (ensures realizes left right h x (ltree left right h x) /\
                   distinct (boxes (ltree left right h x)))
  = reveal_opaque (`%unshared) (unshared #a); reveal_opaque (`%ltree) (ltree #a); reveal_opaque (`%wf) (wf #a);
    closed_realizes left right (fuel h) h x

(* ------------------------------------------------------------------------------------ *)
(* One step down                                                                         *)

/// A non-null unshared pointer in the heap is a node over two unshared, disjoint subtrees that do not
/// contain it. Fires where a body has read the node.
let unshared_step (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires unshared left right h x /\ mem h x /\ B.is_null x == false)
          (ensures (let r = get h x in
                    ltree left right h x ==
                      T.Branch (ltree left right h (left r)) (x, r) (ltree left right h (right r)) /\
                    unshared left right h (left r) /\ unshared left right h (right r) /\
                    ~ (L.memP x (boxes (ltree left right h (left r)))) /\
                    ~ (L.memP x (boxes (ltree left right h (right r)))) /\
                    disjoint (boxes (ltree left right h (left r))) (boxes (ltree left right h (right r)))))
          [SMTPat (unshared left right h x); SMTPat (get h x)]
  = reveal_opaque (`%unshared) (unshared #a); reveal_opaque (`%ltree) (ltree #a); reveal_opaque (`%wf) (wf #a);
    unshared_elim left right h x;
    let t = ltree left right h x in
    if T.Leaf? t then ()
    else begin
      let T.Branch l (b, r) rr = t in
      unshared_intro left right h (left r) l;
      unshared_intro left right h (right r) rr
    end

let unshared_null (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires B.is_null x) (ensures unshared left right h x /\ ltree left right h x == T.Leaf)
          [SMTPat (unshared left right h x)]
  = reveal_opaque (`%unshared) (unshared #a); reveal_opaque (`%ltree) (ltree #a)

let ltree_null (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires B.is_null x) (ensures ltree left right h x == T.Leaf)
          [SMTPat (ltree left right h x)]
  = reveal_opaque (`%ltree) (ltree #a)

/// A non-null unshared pointer is in the heap.
let unshared_mem (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires unshared left right h x /\ B.is_null x == false) (ensures mem h x)
          [SMTPat (unshared left right h x)]
  = reveal_opaque (`%unshared) (unshared #a); reveal_opaque (`%ltree) (ltree #a); reveal_opaque (`%wf) (wf #a);
    mem_of_wf left right h x

let unshared_wf (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires unshared left right h x) (ensures wf left right h x)
          [SMTPat (unshared left right h x)]
  = reveal_opaque (`%unshared) (unshared #a); reveal_opaque (`%ltree) (ltree #a)

(* ------------------------------------------------------------------------------------ *)
(* Writes                                                                                *)

let rec realizes_upd (#a: Type0) (left right: a -> B.box a) (h: heap a) (y: B.box a)
    (t: T.tree (B.box a & a)) (b: B.box a) (v: a)
  : Lemma (requires realizes left right h y t /\ ~ (L.memP b (boxes t)))
          (ensures realizes left right (upd h b v) y t)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (_, r) rr ->
      realizes_upd left right h (left r) l b v;
      realizes_upd left right h (right r) rr b v

/// A write to a box outside what `y` reaches leaves `y`'s tree alone.
let upd_outside (#a: Type0) (left right: a -> B.box a) (h: heap a) (y b: B.box a) (v: a)
  : Lemma (requires unshared left right h y /\ ~ (L.memP b (boxes (ltree left right h y))))
          (ensures unshared left right (upd h b v) y /\
                   ltree left right (upd h b v) y == ltree left right h y)
          [SMTPatOr [[SMTPat (ltree left right (upd h b v) y)]; [SMTPat (unshared left right (upd h b v) y)]]]
  = unshared_elim left right h y;
    realizes_upd left right h y (ltree left right h y) b v;
    unshared_intro left right (upd h b v) y (ltree left right h y)

/// A write to a node whose new children reach disjoint trees not containing it makes it the
/// root of exactly those trees.
let upd_node (#a: Type0) (left right: a -> B.box a) (h: heap a) (b: B.box a) (v: a)
  : Lemma (requires mem h b /\ B.is_null b == false /\
                    unshared left right h (left v) /\ unshared left right h (right v) /\
                    ~ (L.memP b (boxes (ltree left right h (left v)))) /\
                    ~ (L.memP b (boxes (ltree left right h (right v)))) /\
                    disjoint (boxes (ltree left right h (left v))) (boxes (ltree left right h (right v))))
          (ensures unshared left right (upd h b v) b /\
                   ltree left right (upd h b v) b ==
                     T.Branch (ltree left right h (left v)) (b, v) (ltree left right h (right v)))
          [SMTPatOr [[SMTPat (ltree left right (upd h b v) b)]; [SMTPat (unshared left right (upd h b v) b)]]]
  = let l = ltree left right h (left v) in
    let rr = ltree left right h (right v) in
    unshared_elim left right h (left v);
    unshared_elim left right h (right v);
    realizes_upd left right h (left v) l b v;
    realizes_upd left right h (right v) rr b v;
    unshared_intro left right (upd h b v) b (T.Branch l (b, v) rr)

/// The heap a write leaves still holds every box it held.
let mem_upd (#a: Type0) (h: heap a) (b y: B.box a) (v: a)
  : Lemma (ensures mem (upd h b v) y <==> mem h y) [SMTPat (mem (upd h b v) y)]
  = ()

(* ------------------------------------------------------------------------------------ *)
(* Allocation                                                                            *)

let rec realizes_cons (#a: Type0) (left right: a -> B.box a) (h: heap a) (y: B.box a)
    (t: T.tree (B.box a & a)) (b: B.box a) (v: a)
  : Lemma (requires realizes left right h y t /\ ~ (mem h b))
          (ensures realizes left right ((b, v) :: h) y t)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (_, r) rr ->
      realizes_cons left right h (left r) l b v;
      realizes_cons left right h (right r) rr b v

let alloc_outside (#a: Type0) (left right: a -> B.box a) (h: heap a) (y b: B.box a) (v: a)
  : Lemma (requires unshared left right h y /\ ~ (mem h b))
          (ensures unshared left right ((b, v) :: h) y /\
                   ltree left right ((b, v) :: h) y == ltree left right h y /\
                   ~ (L.memP b (boxes (ltree left right h y))))
          [SMTPatOr [[SMTPat (ltree left right ((b, v) :: h) y)]; [SMTPat (unshared left right ((b, v) :: h) y)]]]
  = unshared_elim left right h y;
    FStar.Classical.move_requires (realizes_mem left right h y (ltree left right h y)) b;
    realizes_cons left right h y (ltree left right h y) b v;
    unshared_intro left right ((b, v) :: h) y (ltree left right h y)

/// A fresh node over two unshared, disjoint subtrees is the root of exactly those.
let alloc_node (#a: Type0) (left right: a -> B.box a) (h: heap a) (b: B.box a) (v: a)
  : Lemma (requires ~ (mem h b) /\ B.is_null b == false /\
                    unshared left right h (left v) /\ unshared left right h (right v) /\
                    disjoint (boxes (ltree left right h (left v))) (boxes (ltree left right h (right v))))
          (ensures unshared left right ((b, v) :: h) b /\
                   ltree left right ((b, v) :: h) b ==
                     T.Branch (ltree left right h (left v)) (b, v) (ltree left right h (right v)))
          [SMTPatOr [[SMTPat (ltree left right ((b, v) :: h) b)]; [SMTPat (unshared left right ((b, v) :: h) b)]]]
  = let l = ltree left right h (left v) in
    let rr = ltree left right h (right v) in
    unshared_elim left right h (left v);
    unshared_elim left right h (right v);
    FStar.Classical.move_requires (realizes_mem left right h (left v) l) b;
    FStar.Classical.move_requires (realizes_mem left right h (right v) rr) b;
    realizes_cons left right h (left v) l b v;
    realizes_cons left right h (right v) rr b v;
    unshared_intro left right ((b, v) :: h) b (T.Branch l (b, v) rr)

/// A fresh leaf node (both children null).
let alloc_leaf (#a: Type0) (left right: a -> B.box a) (h: heap a) (b: B.box a) (v: a)
  : Lemma (requires ~ (mem h b) /\ B.is_null b == false /\ B.is_null (left v) /\ B.is_null (right v))
          (ensures unshared left right ((b, v) :: h) b /\
                   ltree left right ((b, v) :: h) b == T.Branch T.Leaf (b, v) T.Leaf)
          [SMTPatOr [[SMTPat (ltree left right ((b, v) :: h) b)]; [SMTPat (unshared left right ((b, v) :: h) b)]]]
  = unshared_null left right h (left v);
    unshared_null left right h (right v);
    alloc_node left right h b v

/// A fresh box is in no tree of the heap it was not in.
let fresh_outside (#a: Type0) (left right: a -> B.box a) (h: heap a) (y b: B.box a)
  : Lemma (requires unshared left right h y /\ ~ (mem h b))
          (ensures ~ (L.memP b (boxes (ltree left right h y))))
          [SMTPat (unshared left right h y); SMTPat (mem h b)]
  = unshared_elim left right h y;
    FStar.Classical.move_requires (realizes_mem left right h y (ltree left right h y)) b

let mem_cons (#a: Type0) (h: heap a) (b y: B.box a) (v: a)
  : Lemma (ensures mem ((b, v) :: h) y <==> y == b \/ mem h y) [SMTPat (mem ((b, v) :: h) y)]
  = ()

(* ------------------------------------------------------------------------------------ *)
(* Frames                                                                                *)

/// R27.16. `h1` holds every box `h0` held, and every one outside `s` as it was.
let framed (#a: Type0) (h0 h1: heap a) (s: list (B.box a)) : prop =
  (forall (y: B.box a). mem h0 y ==> mem h1 y) /\
  (forall (y: B.box a). mem h0 y /\ ~ (L.memP y s) ==> lookup h1 y == lookup h0 y)

/// The frame of what `x` reaches in `h0`.
let framed_at (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (x: B.box a) : prop =
  framed h0 h1 (boxes (ltree left right h0 x))

/// R27.16. What a method that re-links the tree at `x` leaves: every box outside the tree
/// `x` reached is as it was, and the tree `y` now reaches is built of boxes of that tree and
/// of boxes allocated since.
let reshaped (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (x y: B.box a) : prop =
  framed h0 h1 (boxes (ltree left right h0 x)) /\
  (forall (z: B.box a). L.memP z (boxes (ltree left right h1 y)) ==>
                        L.memP z (boxes (ltree left right h0 x)) \/ ~ (mem h0 z))

let rec realizes_framed (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (y: B.box a)
    (t: T.tree (B.box a & a)) (s: list (B.box a))
  : Lemma (requires realizes left right h0 y t /\ framed h0 h1 s /\ disjoint (boxes t) s)
          (ensures realizes left right h1 y t)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (_, r) rr ->
      realizes_framed left right h0 h1 (left r) l s;
      realizes_framed left right h0 h1 (right r) rr s

/// A tree disjoint from what a framed change touched is the same tree after it.
let framed_outside (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (s: list (B.box a))
    (y: B.box a)
  : Lemma (requires unshared left right h0 y /\ framed h0 h1 s /\
                    disjoint (boxes (ltree left right h0 y)) s)
          (ensures unshared left right h1 y /\ ltree left right h1 y == ltree left right h0 y)
  = unshared_elim left right h0 y;
    realizes_framed left right h0 h1 y (ltree left right h0 y) s;
    unshared_intro left right h1 y (ltree left right h0 y)

/// A frame is a frame of any larger set.
let framed_mono (#a: Type0) (h0 h1: heap a) (s s': list (B.box a))
  : Lemma (requires framed h0 h1 s /\ (forall (y: B.box a). L.memP y s ==> L.memP y s'))
          (ensures framed h0 h1 s')
  = ()

/// R27.16. Re-linkings compose.
let reshaped_trans (#a: Type0) (left right: a -> B.box a) (h0 h1 h2: heap a) (x y z: B.box a)
  : Lemma (requires reshaped left right h0 h1 x y /\ reshaped left right h1 h2 y z)
          (ensures reshaped left right h0 h2 x z)
          [SMTPat (reshaped left right h0 h1 x y); SMTPat (reshaped left right h1 h2 y z)]
  = ()

/// R27.16. A method that re-linked the subtree under a child of `x` from `c` to `c'` left
/// `x` and its other child as they were, and the new subtree disjoint from both. When the
/// child's root did not move, `x` is again the root of an unshared tree, and the change is
/// a re-linking at `x`.
let reshaped_child (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (x c c': B.box a)
  : Lemma (requires unshared left right h0 x /\ mem h0 x /\ B.is_null x == false /\
                    (c == left (get h0 x) \/ c == right (get h0 x)) /\
                    reshaped left right h0 h1 c c' /\ unshared left right h1 c')
          (ensures (let r = get h0 x in
                    let s = if c == left r then right r else left r in
                    mem h1 x /\ get h1 x == r /\
                    unshared left right h1 s /\ ltree left right h1 s == ltree left right h0 s /\
                    ~ (L.memP x (boxes (ltree left right h1 c'))) /\
                    ~ (L.memP x (boxes (ltree left right h1 s))) /\
                    disjoint (boxes (ltree left right h1 c')) (boxes (ltree left right h1 s)) /\
                    framed h0 h1 (boxes (ltree left right h0 x)) /\
                    (forall (z: B.box a). L.memP z (boxes (ltree left right h1 c')) ==>
                        L.memP z (boxes (ltree left right h0 x)) \/ ~ (mem h0 z)) /\
                    (c' == c ==> unshared left right h1 x /\ reshaped left right h0 h1 x x /\
                                 ltree left right h1 x ==
                                   (if c == left r
                                    then T.Branch (ltree left right h1 c') (x, r) (ltree left right h1 s)
                                    else T.Branch (ltree left right h1 s) (x, r) (ltree left right h1 c')))))
          [SMTPat (reshaped left right h0 h1 c c'); SMTPat (unshared left right h0 x); SMTPat (get h0 x)]
  = let r = get h0 x in
    unshared_step left right h0 x;
    let s = if c == left r then right r else left r in
    let bc = boxes (ltree left right h0 c) in
    framed_outside left right h0 h1 bc s;
    let bx = boxes (ltree left right h0 x) in
    framed_mono h0 h1 bc bx;
    unshared_elim left right h0 x;
    if FStar.IndefiniteDescription.strong_excluded_middle (c' == c) then begin
      let t1 = if c == left r
               then T.Branch (ltree left right h1 c') (x, r) (ltree left right h1 s)
               else T.Branch (ltree left right h1 s) (x, r) (ltree left right h1 c') in
      unshared_elim left right h1 c';
      unshared_elim left right h1 s;
      unshared_intro left right h1 x t1
    end
