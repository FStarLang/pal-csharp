module Pulse.Lib.CSharp.RegionPath

/// R27.21. Paths into a boxed tree, and the graft that lifts a re-linking under one node to
/// the whole structure. A tree whose nodes are boxes (`ltree`, or any view of it that keeps
/// the boxes) is a *focus*: the path of frames from the root down to one node, and the
/// subtree at that node. A method that re-links the tree under `x` (`reshaped h0 h1 x x`)
/// changes the whole tree by replacing the subtree at `x`; that is `graft`.
///
/// Nothing here is trusted beyond `Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8).

open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree

(* ------------------------------------------------------------------------------------ *)
(* Boxed trees of any payload                                                            *)

let rec nboxes (#r #e: Type0) (t: T.tree (B.box r & e)) : Tot (list (B.box r)) (decreases t) =
  match t with
  | T.Leaf -> []
  | T.Branch l (b, _) rr -> b :: L.append (nboxes l) (nboxes rr)

let rec nboxes_boxes (#a: Type0) (t: T.tree (B.box a & a))
  : Lemma (ensures nboxes t == boxes t) (decreases t) [SMTPat (nboxes t)]
  = match t with T.Leaf -> () | T.Branch l _ rr -> nboxes_boxes l; nboxes_boxes rr

let mem_nboxes_branch (#r #e: Type0) (y: B.box r) (l: T.tree (B.box r & e)) (b: B.box r) (v: e)
    (rr: T.tree (B.box r & e))
  : Lemma (ensures L.memP y (nboxes (T.Branch l (b, v) rr)) <==>
                   y == b \/ L.memP y (nboxes l) \/ L.memP y (nboxes rr))
          [SMTPat (L.memP y (nboxes (T.Branch l (b, v) rr)))]
  = ()

/// The box at the root, or `null`.
let top (#r #e: Type0) (t: T.tree (B.box r & e)) : B.box r =
  match t with T.Leaf -> B.null | T.Branch _ (b, _) _ -> b

/// Every node's payload transformed, its box kept.
let rec bmap (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (t: T.tree (B.box r & e1))
  : Tot (T.tree (B.box r & e2)) (decreases t)
  = match t with
    | T.Leaf -> T.Leaf
    | T.Branch l (b, v) rr -> T.Branch (bmap g l) (b, g b v) (bmap g rr)

let rec nboxes_bmap (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (t: T.tree (B.box r & e1))
  : Lemma (ensures nboxes (bmap g t) == nboxes t) (decreases t) [SMTPat (nboxes (bmap g t))]
  = match t with T.Leaf -> () | T.Branch l _ rr -> nboxes_bmap g l; nboxes_bmap g rr

let top_bmap (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (t: T.tree (B.box r & e1))
  : Lemma (ensures top (bmap g t) == top t) [SMTPat (top (bmap g t))]
  = ()

(* ------------------------------------------------------------------------------------ *)
(* Frames                                                                                *)

/// One step of a path: the node left behind, the side the path took, and the subtree on
/// the other side.
noeq type frame (r e: Type0) = {
  went_right: bool;
  fbox: B.box r;
  fval: e;
  fsib: T.tree (B.box r & e);
}

let fill (#r #e: Type0) (f: frame r e) (s: T.tree (B.box r & e)) : T.tree (B.box r & e) =
  if f.went_right then T.Branch f.fsib (f.fbox, f.fval) s else T.Branch s (f.fbox, f.fval) f.fsib

/// A path, innermost frame first, closed over the subtree at its end.
let rec plug (#r #e: Type0) (fs: list (frame r e)) (s: T.tree (B.box r & e))
  : Tot (T.tree (B.box r & e)) (decreases fs)
  = match fs with
    | [] -> s
    | f :: rest -> plug rest (fill f s)

let rec fboxes (#r #e: Type0) (fs: list (frame r e)) : Tot (list (B.box r)) (decreases fs) =
  match fs with
  | [] -> []
  | f :: rest -> f.fbox :: L.append (nboxes f.fsib) (fboxes rest)

let rec mem_plug (#r #e: Type0) (y: B.box r) (fs: list (frame r e)) (s: T.tree (B.box r & e))
  : Lemma (ensures L.memP y (nboxes (plug fs s)) <==> L.memP y (fboxes fs) \/ L.memP y (nboxes s))
          (decreases fs)
          [SMTPat (L.memP y (nboxes (plug fs s)))]
  = match fs with
    | [] -> ()
    | f :: rest -> mem_plug y rest (fill f s)

let rec distinct_plug (#r #e: Type0) (fs: list (frame r e)) (s: T.tree (B.box r & e))
  : Lemma (ensures distinct (nboxes (plug fs s)) <==>
                   distinct (fboxes fs) /\ distinct (nboxes s) /\ disjoint (fboxes fs) (nboxes s))
          (decreases fs)
          [SMTPat (distinct (nboxes (plug fs s)))]
  = match fs with
    | [] -> ()
    | f :: rest -> distinct_plug rest (fill f s)

let mapf (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (f: frame r e1) : frame r e2 =
  { went_right = f.went_right; fbox = f.fbox; fval = g f.fbox f.fval; fsib = bmap g f.fsib }

let rec bmap_plug (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (fs: list (frame r e1))
    (s: T.tree (B.box r & e1))
  : Lemma (ensures bmap g (plug fs s) == plug (L.map (mapf g) fs) (bmap g s)) (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest -> bmap_plug g rest (fill f s)

(* ------------------------------------------------------------------------------------ *)
(* Focus                                                                                 *)

let rec mem_box (#r #e: Type0) (x: B.box r) (t: T.tree (B.box r & e)) : Tot bool (decreases t) =
  match t with
  | T.Leaf -> false
  | T.Branch l (b, _) rr -> eq_box b x || mem_box x l || mem_box x rr

let rec mem_box_nboxes (#r #e: Type0) (x: B.box r) (t: T.tree (B.box r & e))
  : Lemma (ensures mem_box x t <==> L.memP x (nboxes t)) (decreases t)
          [SMTPat (mem_box x t)]
  = match t with T.Leaf -> () | T.Branch l _ rr -> mem_box_nboxes x l; mem_box_nboxes x rr

/// The path from the root to the first node (pre-order) whose box is `x`, and its subtree.
let rec focus_acc (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) (acc: list (frame r e))
  : Tot (list (frame r e) & T.tree (B.box r & e)) (decreases t)
  = match t with
    | T.Leaf -> (acc, t)
    | T.Branch l (b, v) rr ->
      if eq_box b x then (acc, t)
      else if mem_box x l then focus_acc l x ({ went_right = false; fbox = b; fval = v; fsib = rr } :: acc)
      else focus_acc rr x ({ went_right = true; fbox = b; fval = v; fsib = l } :: acc)

let focus (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) = focus_acc t x []

/// The subtree at `x`, and the tree with it replaced.
let sub (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) : T.tree (B.box r & e) =
  snd (focus t x)

let replace (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) (s: T.tree (B.box r & e))
  : T.tree (B.box r & e) =
  plug (fst (focus t x)) s

let rec focus_acc_plug (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) (acc: list (frame r e))
  : Lemma (ensures plug (fst (focus_acc t x acc)) (snd (focus_acc t x acc)) == plug acc t)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (b, v) rr ->
      if eq_box b x then ()
      else if mem_box x l then focus_acc_plug l x ({ went_right = false; fbox = b; fval = v; fsib = rr } :: acc)
      else focus_acc_plug rr x ({ went_right = true; fbox = b; fval = v; fsib = l } :: acc)

let rec focus_acc_top (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) (acc: list (frame r e))
  : Lemma (requires L.memP x (nboxes t)) (ensures top (snd (focus_acc t x acc)) == x) (decreases t)
  = match t with
    | T.Branch l (b, v) rr ->
      if eq_box b x then ()
      else if mem_box x l then focus_acc_top l x ({ went_right = false; fbox = b; fval = v; fsib = rr } :: acc)
      else focus_acc_top rr x ({ went_right = true; fbox = b; fval = v; fsib = l } :: acc)

let rec focus_acc_app (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) (acc: list (frame r e))
  : Lemma (ensures focus_acc t x acc == (L.append (fst (focus_acc t x [])) acc, snd (focus_acc t x [])))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (b, v) rr ->
      if eq_box b x then ()
      else if mem_box x l then begin
        let f = { went_right = false; fbox = b; fval = v; fsib = rr } in
        focus_acc_app l x (f :: acc); focus_acc_app l x [f];
        L.append_assoc (fst (focus_acc l x [])) [f] acc
      end else begin
        let f = { went_right = true; fbox = b; fval = v; fsib = l } in
        focus_acc_app rr x (f :: acc); focus_acc_app rr x [f];
        L.append_assoc (fst (focus_acc rr x [])) [f] acc
      end

/// A tree is its focus at any box it holds.
let focus_plug (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r)
  : Lemma (ensures t == plug (fst (focus t x)) (sub t x) /\
                   (L.memP x (nboxes t) ==> top (sub t x) == x))
          [SMTPat (focus t x)]
  = focus_acc_plug t x [];
    FStar.Classical.move_requires (focus_acc_top t x) []

let frame_eta (#r #e: Type0) (f: frame r e)
  : Lemma (f == { went_right = f.went_right; fbox = f.fbox; fval = f.fval; fsib = f.fsib })
  = ()

let focus_fill (#r #e: Type0) (f: frame r e) (u: T.tree (B.box r & e)) (x: B.box r)
  : Lemma (requires distinct (nboxes (fill f u)) /\ L.memP x (nboxes u))
          (ensures focus (fill f u) x == focus_acc u x [f])
  = frame_eta f;
    mem_box_nboxes x f.fsib; mem_box_nboxes x u;
    assert (~ (f.fbox == x));
    if f.went_right then assert (~ (L.memP x (nboxes f.fsib)))

let rec focus_in_plug (#r #e: Type0) (fs: list (frame r e)) (u: T.tree (B.box r & e)) (x: B.box r)
  : Lemma (requires distinct (nboxes (plug fs u)) /\ L.memP x (nboxes u))
          (ensures focus (plug fs u) x == (L.append (fst (focus u x)) fs, snd (focus u x)))
          (decreases fs)
  = match fs with
    | [] -> L.append_l_nil (fst (focus u x))
    | f :: rest ->
      let u' = fill f u in
      focus_in_plug rest u' x;
      distinct_plug rest u';
      focus_fill f u x;
      focus_acc_app u x [f];
      L.append_assoc (fst (focus u x)) [f] rest;
      mem_box_nboxes x f.fsib

/// A path closed over a subtree is the focus at that subtree's root, when no box repeats.
let focus_unique (#r #e: Type0) (fs: list (frame r e)) (s: T.tree (B.box r & e))
  : Lemma (requires distinct (nboxes (plug fs s)) /\ T.Branch? s)
          (ensures focus (plug fs s) (top s) == (fs, s))
  = focus_in_plug fs s (top s)

let rec focus_bmap_acc (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (t: T.tree (B.box r & e1))
    (x: B.box r) (acc: list (frame r e1))
  : Lemma (ensures focus_acc (bmap g t) x (L.map (mapf g) acc) ==
                   (L.map (mapf g) (fst (focus_acc t x acc)), bmap g (snd (focus_acc t x acc))))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (b, v) rr ->
      mem_box_nboxes x l; mem_box_nboxes x (bmap g l);
      if eq_box b x then ()
      else if mem_box x l then focus_bmap_acc g l x ({ went_right = false; fbox = b; fval = v; fsib = rr } :: acc)
      else focus_bmap_acc g rr x ({ went_right = true; fbox = b; fval = v; fsib = l } :: acc)

/// Focus commutes with a payload map.
let focus_bmap (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (t: T.tree (B.box r & e1)) (x: B.box r)
  : Lemma (ensures focus (bmap g t) x == (L.map (mapf g) (fst (focus t x)), bmap g (sub t x)))
          [SMTPat (focus (bmap g t) x)]
  = focus_bmap_acc g t x []

let sub_bmap (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (t: T.tree (B.box r & e1)) (x: B.box r)
  : Lemma (ensures sub (bmap g t) x == bmap g (sub t x)) [SMTPat (sub (bmap g t) x)]
  = focus_bmap g t x

let replace_bmap (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (t: T.tree (B.box r & e1)) (x: B.box r)
    (s: T.tree (B.box r & e1))
  : Lemma (ensures replace (bmap g t) x (bmap g s) == bmap g (replace t x s))
          [SMTPat (replace (bmap g t) x (bmap g s))]
  = focus_bmap g t x; bmap_plug g (fst (focus t x)) s

(* ------------------------------------------------------------------------------------ *)
(* Paths in a heap                                                                       *)

let rec realizes_nonnull (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
    (t: T.tree (B.box a & a)) (y: B.box a)
  : Lemma (requires realizes left right h x t /\ L.memP y (boxes t)) (ensures B.is_null y == false)
          (decreases t)
  = match t with
    | T.Branch l (b, r) rr ->
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (boxes l))
      then realizes_nonnull left right h (left r) l y
      else if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (boxes rr))
      then realizes_nonnull left right h (right r) rr y
      else ()

let rec realizes_plug_sub (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
    (fs: list (frame a a)) (u: T.tree (B.box a & a))
  : Lemma (requires realizes left right h x (plug fs u))
          (ensures realizes left right h (top u) u)
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest ->
      realizes_plug_sub left right h x rest (fill f u)

/// The subtree an unshared pointer's tree has at one of its boxes is what that box reaches.
let sub_ltree (#a: Type0) (left right: a -> B.box a) (h: heap a) (root x: B.box a)
  : Lemma (requires unshared left right h root /\ L.memP x (boxes (ltree left right h root)))
          (ensures unshared left right h x /\ sub (ltree left right h root) x == ltree left right h x)
          [SMTPat (unshared left right h root); SMTPat (sub (ltree left right h root) x)]
  = let t = ltree left right h root in
    unshared_elim left right h root;
    focus_plug t x;
    let (fs, s) = focus t x in
    realizes_plug_sub left right h root fs s;
    distinct_plug fs s;
    unshared_intro left right h x s

let rec realizes_plug_framed (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (x: B.box a)
    (fs: list (frame a a)) (u0 u1: T.tree (B.box a & a)) (s: list (B.box a))
  : Lemma (requires realizes left right h0 x (plug fs u0) /\ realizes left right h1 (top u1) u1 /\
                    top u0 == top u1 /\ framed h0 h1 s /\ disjoint (fboxes fs) s)
          (ensures realizes left right h1 x (plug fs u1))
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest ->
      realizes_plug_sub left right h0 x rest (fill f u0);
      realizes_mem left right h0 (top (fill f u0)) (fill f u0) f.fbox;
      let r = get h0 f.fbox in
      let sp = if f.went_right then left r else right r in
      realizes_framed left right h0 h1 sp f.fsib s;
      realizes_plug_framed left right h0 h1 x rest (fill f u0) (fill f u1) s

/// R27.21. A re-linking at `x` inside the tree `root` reaches is a replacement of the subtree
/// at `x`: the path to `x` is untouched, so the whole tree is the old path closed over the new
/// subtree.
let graft (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (root x: B.box a)
  : Lemma (requires unshared left right h0 root /\ L.memP x (boxes (ltree left right h0 root)) /\
                    reshaped left right h0 h1 x x /\ unshared left right h1 x)
          (ensures unshared left right h1 root /\
                   ltree left right h1 root == replace (ltree left right h0 root) x (ltree left right h1 x))
          [SMTPat (reshaped left right h0 h1 x x); SMTPat (unshared left right h0 root);
           SMTPat (ltree left right h1 root)]
  = let t = ltree left right h0 root in
    unshared_elim left right h0 root;
    sub_ltree left right h0 root x;
    focus_plug t x;
    let (fs, s) = focus t x in
    let s1 = ltree left right h1 x in
    unshared_elim left right h1 x;
    unshared_elim left right h0 x;
    distinct_plug fs s;
    let aux (y: B.box a) : Lemma (L.memP y (fboxes fs) ==> mem h0 y) =
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (fboxes fs))
      then realizes_mem left right h0 root t y else () in
    FStar.Classical.forall_intro aux;
    realizes_plug_sub left right h0 root fs s;
    realizes_nonnull left right h0 root t x;
    assert (top s1 == x);
    realizes_plug_framed left right h0 h1 root fs s s1 (boxes s);
    distinct_plug fs s1;
    unshared_intro left right h1 root (plug fs s1)

/// A re-linking at `x` also re-links the whole tree at `root`.
let graft_reshaped (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (root x: B.box a)
  : Lemma (requires unshared left right h0 root /\ L.memP x (boxes (ltree left right h0 root)) /\
                    reshaped left right h0 h1 x x /\ unshared left right h1 x)
          (ensures reshaped left right h0 h1 root root)
          [SMTPat (reshaped left right h0 h1 x x); SMTPat (unshared left right h0 root);
           SMTPat (reshaped left right h0 h1 root root)]
  = graft left right h0 h1 root x;
    let t = ltree left right h0 root in
    sub_ltree left right h0 root x;
    focus_plug t x;
    let (fs, s) = focus t x in
    unshared_elim left right h0 root;
    let s1 = ltree left right h1 x in
    nboxes_boxes t; nboxes_boxes s; nboxes_boxes s1; nboxes_boxes (plug fs s1);
    let in_t (z: B.box a) : Lemma (L.memP z (boxes s) ==> L.memP z (boxes t)) =
      mem_plug z fs s in
    FStar.Classical.forall_intro in_t;
    framed_mono h0 h1 (boxes s) (boxes t);
    let in_new (z: B.box a)
      : Lemma (L.memP z (boxes (ltree left right h1 root)) ==> L.memP z (boxes t) \/ ~ (mem h0 z)) =
      mem_plug z fs s1; mem_plug z fs s in
    FStar.Classical.forall_intro in_new

(* ------------------------------------------------------------------------------------ *)
(* The tree of boxes and views                                                           *)

/// R27.26. The tree `x` reaches, each node its box and its view: what `Pal.Nodes(x)` is.
let nodes (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a) (h: heap a)
    (x: B.box a) : GTot (T.tree (B.box a & v)) =
  bmap view (ltree left right h x)

/// The root of what `x` reaches is `x`.
let top_ltree (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires unshared left right h x) (ensures top (ltree left right h x) == x)
          [SMTPat (top (ltree left right h x)); SMTPat (unshared left right h x)]
  = if B.is_null x then ()
    else begin
      unshared_mem left right h x;
      unshared_step left right h x
    end

let rec nboxes_strip_mem (#a: Type0) (t: T.tree (B.box a & a)) (y: B.box a)
  : Lemma (ensures L.memP y (nboxes t) <==> L.memP y (boxes t)) (decreases t)
  = ()

/// A re-linking at `x` that left `x` inside the tree now at `y` (a rotation at `x`, say)
/// replaces the subtree at `x` in the tree at `root`, so long as `root`'s path to `x` was
/// not touched.
let graft_any (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (root x y: B.box a)
  : Lemma (requires unshared left right h0 root /\ L.memP x (boxes (ltree left right h0 root)) /\
                    reshaped left right h0 h1 x y /\ unshared left right h1 y /\
                    L.memP x (boxes (ltree left right h1 y)))
          (ensures unshared left right h1 x /\ unshared left right h1 root /\
                   ltree left right h1 root == replace (ltree left right h0 root) x (ltree left right h1 x) /\
                   reshaped left right h0 h1 root root)
  = sub_ltree left right h1 y x;
    let t = ltree left right h0 root in
    let u = ltree left right h1 y in
    focus_plug u x;
    let (gs, s1) = focus u x in
    distinct_plug gs s1;
    unshared_elim left right h1 y;
    assert (forall (z: B.box a). L.memP z (boxes (ltree left right h1 x)) ==> L.memP z (boxes u));
    assert (reshaped left right h0 h1 x x);
    graft left right h0 h1 root x;
    graft_reshaped left right h0 h1 root x

/// The subtree of what `root` reaches at one of its boxes is what that box reaches.
let nodes_sub (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a) (h: heap a)
    (root x: B.box a)
  : Lemma (requires unshared left right h root /\ L.memP x (nboxes (nodes view left right h root)))
          (ensures unshared left right h x /\ sub (nodes view left right h root) x == nodes view left right h x)
  = nboxes_boxes (ltree left right h root);
    sub_ltree left right h root x;
    sub_bmap view (ltree left right h root) x

/// One node of what `x` reaches: its box, its view, and what its links reach.
let nodes_step (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a) (h: heap a)
    (x: B.box a)
  : Lemma (requires unshared left right h x /\ B.is_null x == false)
          (ensures mem h x /\
                   (let r = get h x in
                    nodes view left right h x ==
                      T.Branch (nodes view left right h (left r)) (x, view x r) (nodes view left right h (right r)) /\
                    unshared left right h (left r) /\ unshared left right h (right r) /\
                    top (nodes view left right h (left r)) == left r /\
                    top (nodes view left right h (right r)) == right r))
  = unshared_mem left right h x;
    unshared_step left right h x;
    let r = get h x in
    top_ltree left right h (left r);
    top_ltree left right h (right r)

(* ------------------------------------------------------------------------------------ *)
(* Re-linking one child                                                                  *)

/// R27.26. What `Node.ReplaceChild(c, c')` leaves: `x` holds the same view, the link that was
/// `c` is `c'` (the right one, if the left was not `c`), and nothing else changed.
let relinked (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a) (h0 h1: heap a)
    (x c c': B.box a) : prop =
  mem h0 x /\ mem h1 x /\ framed h0 h1 [x] /\
  view x (get h1 x) == view x (get h0 x) /\
  (left (get h0 x) == c ==> left (get h1 x) == c' /\ right (get h1 x) == right (get h0 x)) /\
  (~ (left (get h0 x) == c) ==> right (get h1 x) == c' /\ left (get h1 x) == left (get h0 x))

let nboxes_fill (#r #e: Type0) (f g: frame r e) (u: T.tree (B.box r & e))
  : Lemma (requires f.went_right == g.went_right /\ f.fbox == g.fbox /\ f.fsib == g.fsib)
          (ensures nboxes (fill f u) == nboxes (fill g u))
  = ()

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let relink_ltree (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h0 h1: heap a) (root c c': B.box a)
  : Lemma (requires unshared left right h0 root /\
                    L.memP c (boxes (ltree left right h0 root)) /\ B.is_null c == false /\
                    Cons? (fst (focus (ltree left right h0 root) c)) /\
                    unshared left right h0 c' /\
                    distinct (nboxes (replace (ltree left right h0 root) c (ltree left right h0 c'))) /\
                    relinked view left right h0 h1 (Cons?.hd (fst (focus (ltree left right h0 root) c))).fbox c c')
          (ensures unshared left right h1 root /\
                   bmap view (ltree left right h1 root) ==
                     bmap view (replace (ltree left right h0 root) c (ltree left right h0 c')))
  = let t = ltree left right h0 root in
    unshared_elim left right h0 root;
    nboxes_boxes t;
    focus_plug t c;
    let (fs, s) = focus t c in
    let f0 :: rest = fs in
    let p = f0.fbox in
    distinct_plug fs s;
    distinct_plug rest (fill f0 s);
    realizes_plug_sub left right h0 root rest (fill f0 s);
    let r0 = get h0 p in
    let r1 = get h1 p in
    assert (f0.fval == r0);
    let u = ltree left right h0 c' in
    unshared_elim left right h0 c';
    nboxes_boxes u;
    let f1 = { f0 with fval = r1 } in
    let s1 = fill f1 u in
    distinct_plug fs u;
    distinct_plug rest (fill f0 u);
    mem_box_nboxes c f0.fsib;
    realizes_nonnull left right h0 p (fill f0 s) c;
    if f0.went_right then begin
      assert (right r0 == c);
      if FStar.IndefiniteDescription.strong_excluded_middle (left r0 == c) then begin
        assert (T.Branch? f0.fsib);
        assert (L.memP c (nboxes f0.fsib))
      end;
      realizes_framed left right h0 h1 (left r0) f0.fsib [p]
    end else begin
      assert (left r0 == c);
      realizes_framed left right h0 h1 (right r0) f0.fsib [p]
    end;
    nboxes_boxes f0.fsib;
    realizes_framed left right h0 h1 c' u [p];
    assert (realizes left right h1 p s1);
    realizes_plug_framed left right h0 h1 root rest (fill f0 s) s1 [p];
    nboxes_fill f0 f1 u;
    distinct_plug rest s1;
    nboxes_boxes (plug rest s1);
    unshared_intro left right h1 root (plug rest s1);
    bmap_plug view rest s1;
    bmap_plug view rest (fill f0 u)
#pop-options

/// Replacing the subtree at `x` twice is replacing it once, and leaves the path to `x` alone.
let replace_twice (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) (u w: T.tree (B.box r & e))
  : Lemma (requires L.memP x (nboxes t) /\ T.Branch? u /\ top u == x /\ distinct (nboxes (replace t x u)))
          (ensures fst (focus (replace t x u) x) == fst (focus t x) /\
                   sub (replace t x u) x == u /\
                   replace (replace t x u) x w == replace t x w)
  = focus_plug t x;
    let (fs, s) = focus t x in
    focus_unique fs u

/// R27.26. A re-linking from `x` to `y` (a rotation at `x`) seen from `root`: the path to `x`
/// is as it was, closed over what `x` now reaches; and closing it over what `y` reaches
/// instead repeats no box.
let graft_nodes (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h0 h1: heap a) (root x y: B.box a)
  : Lemma (requires unshared left right h0 root /\ L.memP x (nboxes (nodes view left right h0 root)) /\
                    reshaped left right h0 h1 x y /\ unshared left right h1 y /\
                    L.memP x (nboxes (nodes view left right h1 y)))
          (ensures unshared left right h1 x /\ unshared left right h1 root /\
                   nodes view left right h1 root ==
                     replace (nodes view left right h0 root) x (nodes view left right h1 x) /\
                   distinct (nboxes (replace (nodes view left right h0 root) x (nodes view left right h1 y))) /\
                   reshaped left right h0 h1 root root)
  = let t = ltree left right h0 root in
    nboxes_boxes t; nboxes_boxes (ltree left right h1 y);
    graft_any left right h0 h1 root x y;
    replace_bmap view t x (ltree left right h1 x);
    replace_bmap view t x (ltree left right h1 y);
    unshared_elim left right h0 root;
    focus_plug t x;
    let (fs, s) = focus t x in
    let u = ltree left right h1 y in
    unshared_elim left right h1 y;
    nboxes_boxes u;
    distinct_plug fs s;
    let mem_fs (z: B.box a) : Lemma (L.memP z (fboxes fs) ==> mem h0 z /\ ~ (L.memP z (boxes s))) =
      mem_plug z fs s;
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (fboxes fs))
      then realizes_mem left right h0 root t z in
    FStar.Classical.forall_intro mem_fs;
    sub_ltree left right h0 root x;
    assert (s == ltree left right h0 x);
    assert (disjoint (fboxes fs) (nboxes u));
    distinct_plug fs u;
    assert (replace t x u == plug fs u);
    assert (distinct (nboxes (replace t x u)))
