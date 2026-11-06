module Pulse.Lib.CSharp.TopDownRemoveHeap

/// R27.30. `SortedSet<T>.DoRemove`'s top-down removal and `ReplaceNode` over the heap of a
/// region: `TopDownRemove`'s descent and `TopDownSucc`'s replacement, read through `nodes`
/// (the tree of boxes and views a pointer reaches). As in `TopDownHeap`, every definition
/// takes the region class's view and links first (`[RegionOp]`, R27.22), then the arguments
/// the C# side passes; the props are what `Node`'s helpers ensure and what the loop carries,
/// and the lemmas are the ghost steps the C# code calls.
///
/// Nothing here is trusted beyond `Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8).

open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
open Pulse.Lib.CSharp.RegionPath
open Pulse.Lib.CSharp.TopDown
open Pulse.Lib.CSharp.TopDownHeap
open Pulse.Lib.CSharp.TopDownRemove
open Pulse.Lib.CSharp.TopDownSucc
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq

(* ------------------------------------------------------------------------------------ *)
(* What `Node`'s helpers do to the boxes                                                 *)

/// `Merge2Nodes`.
let merged (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x: B.box r) : prop =
  nodes view left right h1 x == merge2n (nodes view left right h0 x)

/// `Rotate(rotation)`, from `x` to the new top `y`.
let rotatedn (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x y: B.box r) (rot: ST.tree_rotation) : prop =
  nodes view left right h1 y == rotn rot (nodes view left right h0 x)

/// `Node.Is2Node`, as its contract has it.
let is2t (#a: Type0) (t: T.tree (a & bool)) : prop =
  ~ (ST.is_red t) /\ ~ (ST.is_red (T.left t)) /\ ~ (ST.is_red (T.right t))

/// `parent.GetSibling(current)`, as its contract has it.
let sibling_of (#r: Type0) (left right: r -> B.box r) (h: heap r) (par cur sib: B.box r) : prop =
  (cur == link_at left h par ==> sib == link_at right h par) /\
  (~ (cur == link_at left h par) ==> sib == link_at left h par)

/// `parent.GetRotation(current, sibling)`, as its contract has it.
let rot_h (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (par cur sib: B.box r) : GTot ST.tree_rotation =
  if FStar.IndefiniteDescription.strong_excluded_middle (cur == link_at left h par)
  then (if ST.is_red (T.left (tree_of view left right h sib)) then ST.RotRightLeft else ST.RotLeft)
  else (if ST.is_red (T.left (tree_of view left right h sib)) then ST.RotRight else ST.RotLeftRight)

(* ------------------------------------------------------------------------------------ *)
(* The loop's states                                                                     *)

/// The loop invariant: the tree at `root` is a set of `k0`'s keys, red-black but for its
/// root, and the path to `cur` is `DoRemove`'s search for `k` (`TopDownRemove.rinv`).
let rinvh (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom: B.box r)
    (found: bool) : prop =
  unshared left right h root /\ ok c k0 (nodes view left right h root) /\
  rdesc c k (nodes view left right h root) cur par gp mt pom found

/// The loop's measure: the size of the subtree at `cur`.
let rmeasure (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root cur: B.box r) : GTot int =
  T.size (sub (nodes view left right h root) cur)

/// After a red sibling is lifted (or with a black one): the parent red, `current` a 2-node.
let rmidh (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom: B.box r)
    (found: bool) (m0: int) : prop =
  unshared left right h root /\ ok c k0 (nodes view left right h root) /\
  mdesc c k (nodes view left right h root) cur par gp mt pom found /\
  rmeasure view left right h root cur == m0

/// After the fix-up: `current` is not a 2-node.
let rfxh (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par mt pom: B.box r)
    (found: bool) (m0: int) : prop =
  unshared left right h root /\ ok c k0 (nodes view left right h root) /\
  fdesc c k (nodes view left right h root) cur par mt pom found /\
  rmeasure view left right h root cur == m0

(* ------------------------------------------------------------------------------------ *)
(* Facts of the path                                                                     *)

let is2_strip (#r #a: Type0) (s: nt r a)
  : Lemma (ensures is2 s <==> (T.Branch? s /\ is2t (strip s)))
  = match s with T.Leaf -> () | T.Branch l _ rr -> ()

/// The frame above the end of a path, in the heap.
let par_at (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root: B.box r) (f0: fr r t) (rest: list (fr r t)) (s: nt r t)
  : Lemma (requires unshared left right h root /\ nodes view left right h root == plug (f0 :: rest) s /\
                    distinct (nboxes (plug (f0 :: rest) s)) /\ all_nonnull (plug (f0 :: rest) s))
          (ensures (let p = f0.fbox in
                    let n = nodes view left right h root in
                    B.is_null p == false /\ mem h p /\ unshared left right h p /\ wf left right h p /\
                    L.memP p (nboxes n) /\
                    nodes view left right h p == fill f0 s /\ sub n p == fill f0 s /\
                    fst (focus n p) == rest /\
                    (let v = get h p in
                     nodes view left right h (left v) == (if f0.went_right then f0.fsib else s) /\
                     nodes view left right h (right v) == (if f0.went_right then s else f0.fsib) /\
                     top (nodes view left right h (left v)) == left v /\
                     top (nodes view left right h (right v)) == right v)))
  = distinct_plug rest (fill f0 s);
    focus_at rest (fill f0 s);
    at_box view left right h root f0.fbox

/// Where the path to a non-null `cur` is.
let cur_at (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (h: heap r) (root: B.box r) (fs: list (fr r t)) (s: nt r t)
    (cur: B.box r)
  : Lemma (requires unshared left right h root /\ ok c k0 (nodes view left right h root) /\
                    nodes view left right h root == plug fs s /\ cur == top s /\ B.is_null cur == false)
          (ensures T.Branch? s /\ L.memP cur (nboxes (nodes view left right h root)) /\
                   mem h cur /\ unshared left right h cur /\ wf left right h cur /\
                   nodes view left right h cur == s /\ sub (nodes view left right h root) cur == s /\
                   fst (focus (nodes view left right h root) cur) == fs /\
                   tree_of view left right h cur == strip s /\
                   ST.rb (strip s) /\ joint_ok fs s /\
                   (forall (u: nt r t). replace (plug fs s) cur u == plug fs u))
  = (match s with T.Leaf -> () | _ -> ok_focus c k0 fs s);
    at_box view left right h root cur;
    tree_strip view left right h cur

(* ------------------------------------------------------------------------------------ *)
(* The descent                                                                           *)

/// Before the loop: the invariant at a non-null `root`.
let r_start (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root: B.box r)
  : Lemma (requires unshared left right h root /\ B.is_null root == false /\
                    ST.keys (tree_of view left right h root) == k0 /\ S.strictly_sorted c k0 /\
                    ST.red_black (tree_of view left right h root))
          (ensures rinvh view left right c k0 k h root root B.null B.null B.null B.null false)
  = start view left right c k0 k h root;
    let n = nodes view left right h root in
    top_ltree left right h root;
    assert (top n == root);
    rdesc_intro c k [] n root B.null B.null B.null B.null false

/// The top of an iteration: `cur` can be read, and if it is not a 2-node there is nothing
/// to fix.
let r_at_cur (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom: B.box r)
    (found: bool)
  : Lemma (requires rinvh view left right c k0 k h root cur par gp mt pom found /\ B.is_null cur == false)
          (ensures mem h cur /\ unshared left right h cur /\ wf left right h cur /\
                   (~ (is2t (tree_of view left right h cur)) ==>
                      rfxh view left right c k0 k h root cur par mt pom found
                        (rmeasure view left right h root cur)))
  = let n = nodes view left right h root in
    let (fs, s) = rdesc_elim c k n cur par gp mt pom found in
    cur_at view left right c k0 h root fs s cur;
    is2_strip s;
    if is2 s then () else fix_not2 c k n cur par gp mt pom found k0

/// `current.ColorRed()` at the root.
let r_fix_root (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1: heap r) (root cur par gp mt pom: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires rinvh view left right c k0 k h root cur par gp mt pom found /\ B.is_null cur == false /\
                    is2t (tree_of view left right h cur) /\ par == B.null /\
                    m0 == rmeasure view left right h root cur /\
                    recolored view left right h h1 cur true /\ unshared left right h1 cur)
          (ensures rfxh view left right c k0 k h1 root cur par mt pom found m0)
  = let n = nodes view left right h root in
    let (fs, s) = rdesc_elim c k n cur par gp mt pom found in
    cur_at view left right c k0 h root fs s cur;
    is2_strip s;
    (match fs with [] -> () | f0 :: _ -> mem_plug f0.fbox fs s);
    assert (fs == []);
    top_ltree left right h root;
    assert (cur == root);
    fix_root c k0 k s cur par gp mt pom found

/// `parent.GetSibling(current)` can be called.
let r_sib_pre (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom: B.box r)
    (found: bool)
  : Lemma (requires rinvh view left right c k0 k h root cur par gp mt pom found /\ B.is_null cur == false /\
                    is2t (tree_of view left right h cur) /\ ~ (par == B.null))
          (ensures mem h par /\ unshared left right h par /\ wf left right h par /\
                   ((cur == link_at left h par /\ ~ (link_at right h par == B.null)) \/
                    (cur == link_at right h par /\ ~ (link_at left h par == B.null))) /\
                   ~ (link_at left h par == link_at right h par))
  = let n = nodes view left right h root in
    let (fs, s) = rdesc_elim c k n cur par gp mt pom found in
    cur_at view left right c k0 h root fs s cur;
    is2_strip s;
    let f0 :: rest = fs in
    par_at view left right h root f0 rest s;
    rb_plug_sub rest (fill f0 s);
    rb_fill f0 s;
    bh_black s;
    bh_branch f0.fsib;
    mem_plug (top f0.fsib) fs s

#push-options "--z3rlimit 40"
/// The sibling: with a red one the parent is black and can be rotated; with a black one the
/// parent is red.
let r_at_sib (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires rinvh view left right c k0 k h root cur par gp mt pom found /\ B.is_null cur == false /\
                    is2t (tree_of view left right h cur) /\ ~ (par == B.null) /\
                    m0 == rmeasure view left right h root cur /\
                    sibling_of left right h par cur sib)
          (ensures mem h sib /\ unshared left right h sib /\ wf left right h sib /\
                   ~ (sib == B.null) /\ (gp == B.null \/ mem h gp) /\
                   (ST.is_red (tree_of view left right h sib) ==>
                      mem h par /\ unshared left right h par /\
                      ~ (ST.is_red (tree_of view left right h par)) /\
                      ~ (T.Leaf? (T.left (tree_of view left right h par))) /\
                      ~ (T.Leaf? (T.right (tree_of view left right h par)))) /\
                   (~ (ST.is_red (tree_of view left right h sib)) ==>
                      rmidh view left right c k0 k h root cur par gp mt pom found m0))
  = let n = nodes view left right h root in
    let (fs, s) = rdesc_elim c k n cur par gp mt pom found in
    cur_at view left right c k0 h root fs s cur;
    is2_strip s;
    let f0 :: rest = fs in
    par_at view left right h root f0 rest s;
    rb_plug_sub rest (fill f0 s);
    rb_fill f0 s;
    bh_black s;
    bh_branch f0.fsib;
    mem_plug (top f0.fsib) fs s;
    assert (nodes view left right h sib == f0.fsib);
    at_box view left right h root sib;
    tree_strip view left right h sib;
    tree_strip view left right h par;
    (match rest with
     | [] -> ()
     | g :: _ -> mem_plug g.fbox fs s; at_box view left right h root gp);
    if nred f0.fsib then ()
    else begin
      fix_direct c k0 k f0 rest s cur par gp mt pom found;
      mdesc_intro c k fs s cur par gp mt pom found
    end
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* `Node.Rotate`                                                                         *)

/// The grandchild a single rotation blackens: left-left for `Right`, right-right for `Left`.
let rot_red (#r: Type0) (left right: r -> B.box r) (h: heap r) (x: B.box r) (side: bool) : B.box r =
  if side then link_at right h (link_at right h x) else link_at left h (link_at left h x)

#push-options "--z3rlimit 60 --fuel 3 --ifuel 1"
let rot_recolor_l (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x: B.box r)
  : Lemma (requires unshared left right h0 x /\ B.is_null x == false /\
                    ST.is_red (T.left (T.left (tree_of view left right h0 x))) /\
                    (let z = rot_red left right h0 x false in
                     recolored view left right h0 h1 z false /\
                     reshaped left right h0 h1 z z /\ unshared left right h1 z))
          (ensures unshared left right h1 x /\ reshaped left right h0 h1 x x /\
                   (match nodes view left right h0 x with
                    | T.Branch (T.Branch ll lv lr) v rr ->
                      nodes view left right h1 x == T.Branch (T.Branch (recolorn ll false) lv lr) v rr
                    | _ -> False))
  = let n0 = nodes view left right h0 x in
    nodes_step view left right h0 x;
    tree_strip view left right h0 x;
    let c = left (get h0 x) in
    nodes_step view left right h0 c;
    let z = left (get h0 c) in
    tree_strip view left right h0 c;
    let T.Branch l (_, xv) rr = n0 in
    let T.Branch cl (_, cv) cr = l in
    let f1 = { went_right = false; fbox = c; fval = cv; fsib = cr } in
    let f2 = { went_right = false; fbox = x; fval = xv; fsib = rr } in
    let s = nodes view left right h0 z in
    assert (fill f1 s == l);
    assert (fill f2 l == n0);
    assert (plug [f1; f2] s == n0);
    unshared_elim left right h0 x;
    nodes_step view left right h0 z;
    focus_at [f1; f2] s;
    graft_at view left right h0 h1 x z

let rot_recolor_r (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x: B.box r)
  : Lemma (requires unshared left right h0 x /\ B.is_null x == false /\
                    ST.is_red (T.right (T.right (tree_of view left right h0 x))) /\
                    (let z = rot_red left right h0 x true in
                     recolored view left right h0 h1 z false /\
                     reshaped left right h0 h1 z z /\ unshared left right h1 z))
          (ensures unshared left right h1 x /\ reshaped left right h0 h1 x x /\
                   (match nodes view left right h0 x with
                    | T.Branch l v (T.Branch rl rv rr) ->
                      nodes view left right h1 x == T.Branch l v (T.Branch rl rv (recolorn rr false))
                    | _ -> False))
  = let n0 = nodes view left right h0 x in
    nodes_step view left right h0 x;
    tree_strip view left right h0 x;
    let c = right (get h0 x) in
    nodes_step view left right h0 c;
    let z = right (get h0 c) in
    tree_strip view left right h0 c;
    let T.Branch l (_, xv) rr = n0 in
    let T.Branch cl (_, cv) cr = rr in
    let f1 = { went_right = true; fbox = c; fval = cv; fsib = cl } in
    let f2 = { went_right = true; fbox = x; fval = xv; fsib = l } in
    let s = nodes view left right h0 z in
    assert (fill f1 s == rr);
    assert (fill f2 rr == n0);
    assert (plug [f1; f2] s == n0);
    unshared_elim left right h0 x;
    nodes_step view left right h0 z;
    focus_at [f1; f2] s;
    graft_at view left right h0 h1 x z
#pop-options

/// What the `Right`/`Left` arms of `Rotate` will give once `RotateRight`/`RotateLeft`
/// returns `y`: the tree `rotn` makes.
let rot_pending (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x: B.box r) (rot: ST.tree_rotation) (w0 w1: bool) : prop =
  forall (h2: heap r) (y: B.box r). {:pattern (rotated view left right h1 h2 x y w0 w1)}
    rotated view left right h1 h2 x y w0 w1 ==> rotatedn view left right h0 h2 x y rot

/// The `Right` or `Left` arm of `Rotate`, after `removeRed.ColorBlack()`.
let rot_single (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x z: B.box r) (side: bool)
  : Lemma (requires unshared left right h0 x /\ B.is_null x == false /\
                    ST.can_rotate (if side then ST.RotLeft else ST.RotRight) (tree_of view left right h0 x) /\
                    z == rot_red left right h0 x side /\
                    (unshared left right h0 z ==>
                     recolored view left right h0 h1 z false /\
                     reshaped left right h0 h1 z z /\ unshared left right h1 z))
          (ensures unshared left right h1 x /\ reshaped left right h0 h1 x x /\
                   rot_pending view left right h0 h1 x (if side then ST.RotLeft else ST.RotRight) side side)
  = tree_strip view left right h0 x;
    unshared_step left right h0 x;
    let c = if side then right (get h0 x) else left (get h0 x) in
    tree_strip view left right h0 c;
    unshared_step left right h0 c;
    if side then rot_recolor_r view left right h0 h1 x else rot_recolor_l view left right h0 h1 x

/// The `RightLeft` or `LeftRight` arm: `rotn` is the double rotation.
let rot_double (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (side: bool)
  : Lemma (ensures rot_pending view left right h0 h0 x
                     (if side then ST.RotLeftRight else ST.RotRightLeft) side (not side))
  = ()

(* ------------------------------------------------------------------------------------ *)
(* A red sibling: `parent.RotateLeft/Right()`, recolour, re-link                         *)

/// The rotation `DoRemove` does at `parent` for a red sibling, as `rotated` has it.
let a_rotated (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h h1: heap r) (par sib: B.box r) : prop =
  (sib == link_at right h par ==> rotated view left right h h1 par sib true true) /\
  (~ (sib == link_at right h par) ==> rotated view left right h h1 par sib false false)

let a_pre (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool) : prop =
  rinvh view left right c k0 k h root cur par gp mt pom found /\ B.is_null cur == false /\
  is2t (tree_of view left right h cur) /\ ~ (par == B.null) /\
  sibling_of left right h par cur sib /\ ST.is_red (tree_of view left right h sib)

#push-options "--z3rlimit 80"
/// The path at a red sibling, and what lifting it does to the parent's subtree.
let a_focus (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool)
  : Ghost (fr r t & list (fr r t) & nt r t)
          (requires a_pre view left right c k0 k h root cur par gp mt pom sib found)
          (ensures fun (f0, rest, s) ->
             let n = nodes view left right h root in
             let fs = f0 :: rest in
             n == plug fs s /\ rinv c k fs s cur par gp mt pom found /\ is2 s /\
             nodes view left right h cur == s /\ T.size (sub n cur) == T.size s /\
             f0.fbox == par /\ mem h par /\ unshared left right h par /\
             L.memP par (nboxes n) /\ nodes view left right h par == fill f0 s /\
             sub n par == fill f0 s /\ fst (focus n par) == rest /\
             nodes view left right h sib == f0.fsib /\ top f0.fsib == sib /\
             nred f0.fsib /\
             (f0.went_right <==> ~ (sib == link_at right h par)) /\
             (let w = f0.went_right in
              let t0 = fill f0 s in
              let u1 = arot w t0 in
              let u3 = recolorn (rcol u1 par true) false in
              let (f0', f1') = a_frames f0 in
              let fs' = f0' :: f1' :: rest in
              rot_for (not w) (not w) t0 == u1 /\
              distinct (nboxes t0) /\
              L.memP par (nboxes u1) /\ top u1 == sib /\
              u3 == fill f1' (fill f0' s) /\ L.memP par (nboxes u3) /\
              plug fs' s == plug rest u3 /\ ok c k0 (plug fs' s) /\
              rmid c k fs' s cur par sib mt (pom_a par mt sib pom) found) /\
             (B.is_null gp <==> rest == []) /\
             (match rest with g :: _ -> g.fbox == gp | [] -> True))
  = let n = nodes view left right h root in
    let (fs, s) = rdesc_elim c k n cur par gp mt pom found in
    cur_at view left right c k0 h root fs s cur;
    is2_strip s;
    let f0 :: rest = fs in
    par_at view left right h root f0 rest s;
    tree_strip view left right h sib;
    distinct_plug rest (fill f0 s);
    (match rest with
     | [] -> ()
     | g :: _ -> mem_plug g.fbox fs s);
    let v = get h par in
    nodes_step view left right h par;
    assert (s == nodes view left right h cur);
    assert (top s == cur);
    distinct_nbranch (nodes view left right h (left v)) par (view par v) (nodes view left right h (right v));
    fix_a c k0 k f0 rest s cur par gp mt pom found;
    (f0, rest, s)
#pop-options

/// After the rotation: `parent` can be recoloured.
let a_mid (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool)
  : Lemma (requires a_pre view left right c k0 k h root cur par gp mt pom sib found /\
                    a_rotated view left right h h1 par sib /\
                    reshaped left right h h1 par sib /\ unshared left right h1 sib)
          (ensures unshared left right h1 par /\ mem h1 par /\
                   L.memP par (nboxes (nodes view left right h1 sib)) /\
                   (gp == B.null \/ mem h1 gp))
  = let (f0, rest, s) = a_focus view left right c k0 k h root cur par gp mt pom sib found in
    let t0 = fill f0 s in
    assert (nodes view left right h1 sib == arot f0.went_right t0);
    nodes_sub view left right h1 sib par;
    match rest with
    | [] -> ()
    | g :: _ ->
      mem_plug gp (f0 :: rest) s;
      at_box view left right h root gp;
      assert (mem h gp)

/// After `parent.ColorRed()`: `sibling` can be recoloured.
let a_red (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1 h2: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool)
  : Lemma (requires a_pre view left right c k0 k h root cur par gp mt pom sib found /\
                    a_rotated view left right h h1 par sib /\
                    reshaped left right h h1 par sib /\ unshared left right h1 sib /\
                    recolored view left right h1 h2 par true /\
                    reshaped left right h1 h2 par par /\ unshared left right h2 par)
          (ensures unshared left right h2 sib /\ reshaped left right h1 h2 sib sib /\
                   (gp == B.null \/ mem h2 gp))
  = a_mid view left right c k0 k h h1 root cur par gp mt pom sib found;
    graft_at view left right h1 h2 sib par

#push-options "--z3rlimit 100"
/// After `ReplaceChildOrRoot(grandParent, parent, sibling)`: `sibling` is the new
/// grandparent, the parent red, and `current` still a 2-node.
let a_end (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1 h2 h3 h4: heap r)
    (root root4 cur par gp mt pom sib: B.box r) (found: bool)
  : Lemma (requires a_pre view left right c k0 k h root cur par gp mt pom sib found /\
                    a_rotated view left right h h1 par sib /\
                    reshaped left right h h1 par sib /\ unshared left right h1 sib /\
                    recolored view left right h1 h2 par true /\
                    reshaped left right h1 h2 par par /\ unshared left right h2 par /\
                    recolored view left right h2 h3 sib false /\
                    reshaped left right h2 h3 sib sib /\ unshared left right h3 sib /\
                    replaced view left right h3 h4 root root4 gp par sib)
          (ensures rmidh view left right c k0 k h4 root4 cur par sib mt (pom_a par mt sib pom) found
                     (rmeasure view left right h root cur))
  = let (f0, rest, s) = a_focus view left right c k0 k h root cur par gp mt pom sib found in
    let n = nodes view left right h root in
    let t0 = fill f0 s in
    let w = f0.went_right in
    let u1 = arot w t0 in
    a_red view left right c k0 k h h1 h2 root cur par gp mt pom sib found;
    assert (nodes view left right h1 sib == u1);
    nodes_sub view left right h1 sib par;
    assert (nodes view left right h2 sib == rcol u1 par true);
    let u3 = recolorn (rcol u1 par true) false in
    assert (nodes view left right h3 sib == u3);
    let (f0', f1') = a_frames f0 in
    let fs' = f0' :: f1' :: rest in
    reshaped_trans left right h h1 h2 par sib sib;
    reshaped_trans left right h h2 h3 par sib sib;
    if B.is_null gp then begin
      assert (rest == []);
      assert (nodes view left right h4 root4 == u3)
    end else begin
      graft_nodes view left right h h3 root par sib;
      let n3 = nodes view left right h3 root in
      top_ltree left right h3 par;
      nboxes_boxes (ltree left right h3 par);
      unshared_step left right h3 par;
      nodes_step view left right h3 par;
      replace_twice n par (nodes view left right h3 par) u3;
      relink_nodes view left right h3 h4 root par sib
    end;
    focus_at fs' s
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* A black sibling: merge, or borrow by a rotation                                       *)

#push-options "--z3rlimit 80"
/// The path at the parent, red, over `current` and a black sibling.
let m_focus (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom: B.box r)
    (found: bool) (m0: int)
  : Ghost (fr r t & list (fr r t) & nt r t)
          (requires rmidh view left right c k0 k h root cur par gp mt pom found m0)
          (ensures fun (f0, rest, s) ->
             let n = nodes view left right h root in
             let fs = f0 :: rest in
             let sib = top f0.fsib in
             n == plug fs s /\ rmid c k fs s cur par gp mt pom found /\ ok c k0 n /\
             is2 s /\ T.size s == m0 /\
             nodes view left right h cur == s /\ mem h cur /\ unshared left right h cur /\
             f0.fbox == par /\ B.is_null par == false /\ mem h par /\ unshared left right h par /\
             L.memP par (nboxes n) /\ nodes view left right h par == fill f0 s /\
             sub n par == fill f0 s /\ fst (focus n par) == rest /\
             distinct (nboxes (fill f0 s)) /\
             B.is_null sib == false /\ mem h sib /\ unshared left right h sib /\
             nodes view left right h sib == f0.fsib /\
             tree_of view left right h sib == strip f0.fsib /\
             tree_of view left right h par == strip (fill f0 s) /\
             tree_of view left right h cur == strip s /\
             (f0.went_right <==> ~ (cur == link_at left h par)) /\
             (f0.went_right ==> link_at right h par == cur /\ link_at left h par == sib) /\
             (f0.went_right == false ==> link_at left h par == cur /\ link_at right h par == sib) /\
             ~ (cur == sib) /\
             (B.is_null gp <==> rest == []) /\
             (match rest with g :: _ -> g.fbox == gp /\ mem h gp | [] -> True))
  = let n = nodes view left right h root in
    let (fs, s) = mdesc_elim c k n cur par gp mt pom found in
    is2_strip s;
    cur_at view left right c k0 h root fs s cur;
    let f0 :: rest = fs in
    par_at view left right h root f0 rest s;
    distinct_plug rest (fill f0 s);
    mem_plug (top f0.fsib) fs s;
    at_box view left right h root (top f0.fsib);
    tree_strip view left right h (top f0.fsib);
    tree_strip view left right h par;
    (match rest with
     | [] -> ()
     | g :: _ -> mem_plug g.fbox fs s; at_box view left right h root g.fbox);
    (f0, rest, s)
#pop-options

/// `parent.GetSibling(current)` can be called after a red sibling was lifted.
let r_mid_pre (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires rmidh view left right c k0 k h root cur par gp mt pom found m0)
          (ensures mem h par /\ unshared left right h par /\ wf left right h par /\
                   ((cur == link_at left h par /\ ~ (link_at right h par == B.null)) \/
                    (cur == link_at right h par /\ ~ (link_at left h par == B.null))) /\
                   ~ (link_at left h par == link_at right h par))
  = let _ = m_focus view left right c k0 k h root cur par gp mt pom found m0 in ()

/// The sibling is black: two 2-nodes are merged, otherwise the parent is rotated.
let r_at_mid (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires rmidh view left right c k0 k h root cur par gp mt pom found m0 /\
                    sibling_of left right h par cur sib)
          (ensures (let ts = tree_of view left right h sib in
                    let tp = tree_of view left right h par in
                    ~ (sib == B.null) /\ mem h sib /\ unshared left right h sib /\ wf left right h sib /\
                    ~ (ST.is_red ts) /\ (gp == B.null \/ mem h gp) /\
                    mem h par /\ unshared left right h par /\ wf left right h par /\
                    mem h cur /\ unshared left right h cur /\
                    ((cur == link_at left h par /\ sib == link_at right h par) \/
                     (cur == link_at right h par /\ sib == link_at left h par)) /\
                    (is2t ts ==>
                       ST.is_red tp /\
                       ~ (T.Leaf? (T.left tp)) /\ ~ (ST.is_red (T.left tp)) /\
                       ~ (ST.is_red (T.left (T.left tp))) /\ ~ (ST.is_red (T.right (T.left tp))) /\
                       ~ (T.Leaf? (T.right tp)) /\ ~ (ST.is_red (T.right tp)) /\
                       ~ (ST.is_red (T.left (T.right tp))) /\ ~ (ST.is_red (T.right (T.right tp)))) /\
                    (~ (is2t ts) ==>
                       ST.is_red (T.left ts) \/ ST.is_red (T.right ts))))
  = let (f0, rest, s) = m_focus view left right c k0 k h root cur par gp mt pom found m0 in
    is2_strip f0.fsib;
    is2_strip s

/// A write to `y`'s colour alone, through a direct field write.
let node_recolor (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h1 h2: heap r) (y: B.box r) (red: bool)
  : Lemma (requires unshared left right h1 y /\ B.is_null y == false /\ mem h1 y /\ mem h2 y /\
                    left (get h2 y) == left (get h1 y) /\ right (get h2 y) == right (get h1 y) /\
                    view y (get h2 y) == (fst (view y (get h1 y)), red) /\
                    framed h1 h2 [y])
          (ensures unshared left right h2 y /\ reshaped left right h1 h2 y y /\
                   nodes view left right h2 y == recolorn (nodes view left right h1 y) red)
  = let v1 = get h1 y in
    let v2 = get h2 y in
    unshared_step left right h1 y;
    let ll = ltree left right h1 (left v1) in
    let lr = ltree left right h1 (right v1) in
    unshared_elim left right h1 (left v1);
    unshared_elim left right h1 (right v1);
    realizes_framed left right h1 h2 (left v1) ll [y];
    realizes_framed left right h1 h2 (right v1) lr [y];
    let lt : T.tree (B.box r & r) = T.Branch ll (y, v2) lr in
    unshared_intro left right h2 y lt;
    unshared_elim left right h1 y;
    framed_mono h1 h2 [y] (boxes (ltree left right h1 y))

#push-options "--z3rlimit 80"
/// After `parent.Merge2Nodes()`: `current` is a 3-node or 4-node.
let r_merge (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires rmidh view left right c k0 k h root cur par gp mt pom found m0 /\
                    sibling_of left right h par cur sib /\ is2t (tree_of view left right h sib) /\
                    merged view left right h h1 par /\
                    reshaped left right h h1 par par /\ unshared left right h1 par)
          (ensures rfxh view left right c k0 k h1 root cur par mt pom found m0)
  = let (f0, rest, s) = m_focus view left right c k0 k h root cur par gp mt pom found m0 in
    is2_strip f0.fsib;
    fix_merge c k0 k f0 rest s cur par gp mt pom found;
    graft_at view left right h h1 root par;
    let s' = recolorn s true in
    let fs' = m_frame f0 :: rest in
    focus_at fs' s';
    fdesc_intro c k fs' s' cur par mt pom found
#pop-options

/// The borrow arm's starting point.
let b_pre (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool) (m0: int) : prop =
  rmidh view left right c k0 k h root cur par gp mt pom found m0 /\
  sibling_of left right h par cur sib /\ ~ (is2t (tree_of view left right h sib))

/// `newGrandParent = parent.Rotate(parent.GetRotation(current, sibling))!`.
let b_s1 (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h h1: heap r) (cur par sib y: B.box r) : prop =
  rotatedn view left right h h1 par y (rot_h view left right h par cur sib) /\
  reshaped left right h h1 par y /\ unshared left right h1 y /\ B.is_null y == false

/// `newGrandParent.Color = parent.Color`.
let b_s2 (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h1 h2: heap r) (par y: B.box r) : prop =
  mem h1 y /\ mem h1 par /\ mem h2 y /\
  left (get h2 y) == left (get h1 y) /\ right (get h2 y) == right (get h1 y) /\
  view y (get h2 y) == (fst (view y (get h1 y)), snd (view par (get h1 par))) /\
  framed h1 h2 [y]

/// `b_s2` from the colour write.
let b_s2_upd (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h1: heap r) (par y: B.box r) (v: r)
  : Lemma (requires mem h1 y /\ mem h1 par /\
                    left v == left (get h1 y) /\ right v == right (get h1 y) /\
                    view y v == (fst (view y (get h1 y)), snd (view par (get h1 par))))
          (ensures b_s2 view left right h1 (upd h1 y v) par y)
          [SMTPat (b_s2 view left right h1 (upd h1 y v) par y)]
  = let h2 = upd h1 y v in
    lookup_upd h1 y y v;
    assert (mem h2 y /\ get h2 y == v);
    assert (framed h1 h2 [y])

/// `parent.ColorBlack()`, `current.ColorRed()`.
let b_col (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h h1: heap r) (x: B.box r) (red: bool) : prop =
  recolored view left right h h1 x red /\ reshaped left right h h1 x x /\ unshared left right h1 x

#push-options "--z3rlimit 100"
/// The path at the parent, and what borrowing does to its subtree.
let b_focus (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp mt pom sib: B.box r)
    (found: bool) (m0: int)
  : Ghost (fr r t & list (fr r t) & nt r t)
          (requires b_pre view left right c k0 k h root cur par gp mt pom sib found m0)
          (ensures fun (f0, rest, s) ->
             let n = nodes view left right h root in
             let fs = f0 :: rest in
             let t0 = fill f0 s in
             let rot = b2_rot f0.went_right f0.fsib in
             let u1 = rotn rot t0 in
             let u2 = recolorn u1 true in
             let u3 = rcol u2 par false in
             let u4 = rcol u3 cur true in
             let (f0', f1') = b2_frames f0 in
             let fs' = f0' :: f1' :: rest in
             n == plug fs s /\ T.size s == m0 /\
             nodes view left right h par == t0 /\ sub n par == t0 /\ fst (focus n par) == rest /\
             L.memP par (nboxes n) /\ B.is_null par == false /\ f0.fbox == par /\
             top s == cur /\ T.Branch? s /\ fred f0 /\
             rot == rot_h view left right h par cur sib /\
             ST.can_rotate rot (strip t0) /\
             L.memP par (nboxes u1) /\
             sub u1 par == T.Branch (T.left (sub u1 par)) (par, f0.fval) (T.right (sub u1 par)) /\
             L.memP par (nboxes u2) /\ L.memP cur (nboxes u3) /\
             top u1 == f1'.fbox /\ ~ (f1'.fbox == par) /\
             u4 == fill f1' (fill f0' (recolorn s true)) /\
             plug fs' (recolorn s true) == plug rest u4 /\
             ok c k0 (plug fs' (recolorn s true)) /\
             rfx c k fs' (recolorn s true) cur par mt (pom_a par mt f1'.fbox pom) found /\
             (B.is_null gp <==> rest == []) /\
             (match rest with g :: _ -> g.fbox == gp /\ mem h gp | [] -> True))
  = let (f0, rest, s) = m_focus view left right c k0 k h root cur par gp mt pom found m0 in
    is2_strip f0.fsib;
    fix_b2 c k0 k f0 rest s cur par gp mt pom found;
    b2_shape f0 s;
    (f0, rest, s)
#pop-options

#push-options "--z3rlimit 80"
/// After the rotation: `parent`'s colour can be read and `newGrandParent`'s written.
let b_rot (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1: heap r) (root cur par gp mt pom sib y: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires b_pre view left right c k0 k h root cur par gp mt pom sib found m0 /\
                    b_s1 view left right h h1 cur par sib y)
          (ensures mem h1 y /\ mem h1 par /\ unshared left right h1 par /\
                   L.memP par (nboxes (nodes view left right h1 y)) /\
                   snd (view par (get h1 par)) == true)
  = let (f0, rest, s) = b_focus view left right c k0 k h root cur par gp mt pom sib found m0 in
    nodes_sub view left right h1 y par;
    nodes_step view left right h1 par

/// After `newGrandParent.Color = parent.Color`: `parent` can be recoloured.
let b_colw (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1 h2: heap r) (root cur par gp mt pom sib y: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires b_pre view left right c k0 k h root cur par gp mt pom sib found m0 /\
                    b_s1 view left right h h1 cur par sib y /\ b_s2 view left right h1 h2 par y)
          (ensures b_s2 view left right h1 h2 par y /\
                   unshared left right h2 y /\ reshaped left right h1 h2 y y /\
                   nodes view left right h2 y == recolorn (nodes view left right h1 y) true /\
                   L.memP par (nboxes (nodes view left right h2 y)) /\
                   mem h2 par /\ unshared left right h2 par)
  = b_rot view left right c k0 k h h1 root cur par gp mt pom sib y found m0;
    node_recolor view left right h1 h2 y true;
    nodes_sub view left right h2 y par

/// After `parent.ColorBlack()`: `current` can be recoloured.
let b_blk (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1 h2 h3: heap r) (root cur par gp mt pom sib y: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires b_pre view left right c k0 k h root cur par gp mt pom sib found m0 /\
                    b_s1 view left right h h1 cur par sib y /\ b_s2 view left right h1 h2 par y /\
                    b_col view left right h2 h3 par false)
          (ensures unshared left right h3 y /\ reshaped left right h2 h3 y y /\
                   nodes view left right h3 y == rcol (nodes view left right h2 y) par false /\
                   L.memP cur (nboxes (nodes view left right h3 y)) /\
                   mem h3 cur /\ unshared left right h3 cur)
  = let (f0, rest, s) = b_focus view left right c k0 k h root cur par gp mt pom sib found m0 in
    b_colw view left right c k0 k h h1 h2 root cur par gp mt pom sib y found m0;
    nodes_sub view left right h2 y par;
    graft_at view left right h2 h3 y par;
    nodes_sub view left right h3 y cur

let reshaped4 (#r: Type0) (left right: r -> B.box r) (h h1 h2 h3 h4: heap r) (par y: B.box r)
  : Lemma (requires reshaped left right h h1 par y /\ reshaped left right h1 h2 y y /\
                    reshaped left right h2 h3 y y /\ reshaped left right h3 h4 y y)
          (ensures reshaped left right h h4 par y)
  = reshaped_trans left right h h1 h2 par y y;
    reshaped_trans left right h h2 h3 par y y;
    reshaped_trans left right h h3 h4 par y y

let mem4 (#r: Type0) (h h1 h2 h3 h4: heap r) (s1 s2 s3 s4: list (B.box r)) (g: B.box r)
  : Lemma (requires framed h h1 s1 /\ framed h1 h2 s2 /\ framed h2 h3 s3 /\ framed h3 h4 s4 /\ mem h g)
          (ensures mem h4 g)
  = ()

/// After `current.ColorRed()`: the rotated subtree is done.
let b_cur (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1 h2 h3 h4: heap r) (root cur par gp mt pom sib y: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires b_pre view left right c k0 k h root cur par gp mt pom sib found m0 /\
                    b_s1 view left right h h1 cur par sib y /\ b_s2 view left right h1 h2 par y /\
                    b_col view left right h2 h3 par false /\ b_col view left right h3 h4 cur true)
          (ensures unshared left right h4 y /\ reshaped left right h h4 par y /\
                   nodes view left right h4 y ==
                     rcol (rcol (recolorn (nodes view left right h1 y) true) par false) cur true /\
                   (gp == B.null \/ mem h4 gp))
  = if B.is_null gp then () else begin
      let _ = b_focus view left right c k0 k h root cur par gp mt pom sib found m0 in
      mem4 h h1 h2 h3 h4 (boxes (ltree left right h par)) [y] (boxes (ltree left right h2 par))
           (boxes (ltree left right h3 cur)) gp
    end;
    b_colw view left right c k0 k h h1 h2 root cur par gp mt pom sib y found m0;
    b_blk view left right c k0 k h h1 h2 h3 root cur par gp mt pom sib y found m0;
    graft_at view left right h3 h4 y cur;
    reshaped4 left right h h1 h2 h3 h4 par y
#pop-options

#push-options "--z3rlimit 100"
/// After `ReplaceChildOrRoot(grandParent, parent, newGrandParent)`.
let b_end (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1 h2 h3 h4 h5: heap r)
    (root root5 cur par gp mt pom sib y: B.box r) (found: bool) (m0: int)
  : Lemma (requires b_pre view left right c k0 k h root cur par gp mt pom sib found m0 /\
                    b_s1 view left right h h1 cur par sib y /\ b_s2 view left right h1 h2 par y /\
                    b_col view left right h2 h3 par false /\ b_col view left right h3 h4 cur true /\
                    replaced view left right h4 h5 root root5 gp par y)
          (ensures rfxh view left right c k0 k h5 root5 cur par mt (pom_a par mt y pom) found m0)
  = let (f0, rest, s) = b_focus view left right c k0 k h root cur par gp mt pom sib found m0 in
    let n = nodes view left right h root in
    let (f0', f1') = b2_frames f0 in
    let s' = recolorn s true in
    let fs' = f0' :: f1' :: rest in
    let u4 = fill f1' (fill f0' s') in
    b_cur view left right c k0 k h h1 h2 h3 h4 root cur par gp mt pom sib y found m0;
    nodes_sub view left right h1 y par;
    nodes_step view left right h1 par;
    top_ltree left right h1 y;
    assert (y == f1'.fbox);
    assert (nodes view left right h4 y == u4);
    if B.is_null gp then begin
      assert (rest == []);
      assert (nodes view left right h5 root5 == u4)
    end else begin
      graft_nodes view left right h h4 root par y;
      let n4 = nodes view left right h4 root in
      top_ltree left right h4 par;
      nboxes_boxes (ltree left right h4 par);
      unshared_step left right h4 par;
      nodes_step view left right h4 par;
      replace_twice n par (nodes view left right h4 par) u4;
      relink_nodes view left right h4 h5 root par y
    end;
    focus_at fs' s';
    fdesc_intro c k fs' s' cur par mt (pom_a par mt y pom) found
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* The step down                                                                         *)

/// After the fix-up, `current` can be read.
let r_at_fx (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par mt pom: B.box r)
    (found: bool) (m0: int)
  : Lemma (requires rfxh view left right c k0 k h root cur par mt pom found m0)
          (ensures B.is_null cur == false /\ mem h cur /\ unshared left right h cur /\
                   wf left right h cur)
  = let n = nodes view left right h root in
    let (fs, s) = fdesc_elim c k n cur par mt pom found in
    assert (L.memP cur (nboxes (plug fs s)));
    cur_at view left right c k0 h root fs s cur

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
/// `order`'s comparison, the match saved when it is 0, and `current` moved to the child the
/// search goes on to: the invariant one level down, at a smaller subtree.
let r_step (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par mt pom: B.box r)
    (found: bool) (m0: int) (o: int) (eq lt: bool)
  : Lemma (requires rfxh view left right c k0 k h root cur par mt pom found m0 /\
                    B.is_null cur == false /\ mem h cur /\
                    o == (if found then -1 else cmp c k (fst (view cur (get h cur)))) /\
                    eq == (o = 0) /\ lt == (o < 0))
          (ensures (eq ==> found == false) /\
                   (let nx = if lt then left (get h cur) else right (get h cur) in
                    rinvh view left right c k0 k h root nx cur par
                      (if eq then cur else mt) (if eq then par else pom) (found || eq) /\
                    0 <= rmeasure view left right h root nx /\ rmeasure view left right h root nx < m0) /\
                   0 <= rmeasure view left right h root (toward left right h cur o) /\
                   rmeasure view left right h root (toward left right h cur o) < m0)
  = assert (toward left right h cur o == (if lt then left (get h cur) else right (get h cur)));
    let n = nodes view left right h root in
    let (fs, s) = fdesc_elim c k n cur par mt pom found in
    cur_at view left right c k0 h root fs s cur;
    at_box view left right h root cur;
    assert (o == rord c k s found);
    step c k0 k fs s cur par mt pom found;
    let ch = rchild s o in
    assert (top ch == toward left right h cur o);
    rdesc_intro c k (rframe s o :: fs) ch (top ch) cur par
      (if o = 0 then cur else mt) (if o = 0 then par else pom) (found || o = 0);
    match ch with
    | T.Branch _ _ _ -> focus_at (rframe s o :: fs) ch
    | T.Leaf ->
      assert (~ (L.memP (B.null #r) (nboxes n)));
      sub_absent n (B.null #r)
#pop-options

/// The search ended at a leaf: if it met no match, `item` is not in the set; otherwise it
/// met it, and `ReplaceNode`'s precondition holds.
let r_at_end (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root par gp mt pom: B.box r)
    (found: bool)
  : Lemma (requires rinvh view left right c k0 k h root B.null par gp mt pom found)
          (ensures (B.is_null mt ==> found == false /\ S.key_index c k0 k < 0) /\
                   (B.is_null mt == false ==>
                      found == true /\ rpre c k0 k (nodes view left right h root) mt pom par gp))
  = let n = nodes view left right h root in
    let (fs, s) = rdesc_elim c k n B.null par gp mt pom found in
    (match s with
     | T.Branch _ _ _ -> assert (L.memP (top s) (nboxes (plug fs s)))
     | T.Leaf -> ());
    if B.is_null mt then end_none c k0 k fs s B.null par gp mt pom found
    else end_found c k0 k fs s B.null par gp mt pom found

(* ------------------------------------------------------------------------------------ *)
(* Re-linking a node over two trees                                                      *)

/// Writes at `x` alone that leave it over `p` and `q`: when `p` and `q` reached disjoint trees
/// without `x`, `x` now reaches the node over both.
let link2 (#a: Type0) (left right: a -> B.box a) (h h': heap a) (x p q: B.box a)
  : Lemma (requires unshared left right h p /\ unshared left right h q /\ B.is_null x == false /\
                    ~ (L.memP x (boxes (ltree left right h p))) /\
                    ~ (L.memP x (boxes (ltree left right h q))) /\
                    disjoint (boxes (ltree left right h p)) (boxes (ltree left right h q)) /\
                    framed h h' [x] /\ mem h' x /\ left (get h' x) == p /\ right (get h' x) == q)
          (ensures unshared left right h' x /\
                   ltree left right h' x ==
                     T.Branch (ltree left right h p) (x, get h' x) (ltree left right h q))
  = let lp = ltree left right h p in
    let lq = ltree left right h q in
    unshared_elim left right h p;
    unshared_elim left right h q;
    realizes_framed left right h h' p lp [x];
    realizes_framed left right h h' q lq [x];
    let t = T.Branch lp (x, get h' x) lq in
    distinct_append (boxes lp) (boxes lq);
    assert (realizes left right h' x t);
    unshared_intro left right h' x t

/// `link2` through the views.
let link2_nodes (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a) (h h': heap a)
    (x p q: B.box a)
  : Lemma (requires unshared left right h p /\ unshared left right h q /\ B.is_null x == false /\
                    ~ (L.memP x (boxes (ltree left right h p))) /\
                    ~ (L.memP x (boxes (ltree left right h q))) /\
                    disjoint (boxes (ltree left right h p)) (boxes (ltree left right h q)) /\
                    framed h h' [x] /\ mem h' x /\ left (get h' x) == p /\ right (get h' x) == q)
          (ensures unshared left right h' x /\
                   nodes view left right h' x ==
                     T.Branch (nodes view left right h p) (x, view x (get h' x)) (nodes view left right h q) /\
                   (forall (z: B.box a). L.memP z (boxes (ltree left right h' x)) <==>
                      z == x \/ L.memP z (boxes (ltree left right h p)) \/
                      L.memP z (boxes (ltree left right h q))))
  = link2 left right h h' x p q

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
/// A re-linking of the subtree at `c` that left it at `c'` (the boxes it reaches are the old
/// subtree's, or new), then `ReplaceChild(c, c')` at `c`'s parent: the whole tree is the old
/// path closed over what `c'` reaches. Unlike `relink_nodes`, `c'` need not be in the old tree,
/// and the old subtree's boxes may have changed in between.
let relink_away (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h0 h1 h2: heap a) (root c c': B.box a)
  : Lemma (requires unshared left right h0 root /\ L.memP c (boxes (ltree left right h0 root)) /\
                    B.is_null c == false /\
                    Cons? (fst (focus (ltree left right h0 root) c)) /\
                    reshaped left right h0 h1 c c' /\ unshared left right h1 c' /\
                    relinked view left right h1 h2
                      (Cons?.hd (fst (focus (ltree left right h0 root) c))).fbox c c')
          (ensures unshared left right h2 root /\
                   nodes view left right h2 root ==
                     replace (nodes view left right h0 root) c (nodes view left right h1 c'))
  = let t = ltree left right h0 root in
    unshared_elim left right h0 root;
    sub_ltree left right h0 root c;
    let (fs, s) = focus t c in
    let f0 :: rest = fs in
    let p = f0.fbox in
    distinct_plug fs s;
    distinct_plug rest (fill f0 s);
    realizes_plug_sub left right h0 root rest (fill f0 s);
    let aux (y: B.box a) : Lemma (L.memP y (fboxes fs) ==> mem h0 y) =
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (fboxes fs))
      then realizes_mem left right h0 root t y else () in
    FStar.Classical.forall_intro aux;
    let r0 = get h0 p in
    let r2 = get h2 p in
    assert (f0.fval == r0);
    let u = ltree left right h1 c' in
    unshared_elim left right h1 c';
    unshared_elim left right h0 c;
    assert (~ (L.memP p (boxes u)));
    let f1 = { f0 with fval = r2 } in
    let s1 = fill f1 u in
    mem_box_nboxes c f0.fsib;
    realizes_nonnull left right h0 p (fill f0 s) c;
    let sb = boxes s in
    let fr : list (B.box a) = p :: sb in
    assert (framed h0 h2 fr);
    let sp = if f0.went_right then left r0 else right r0 in
    if f0.went_right then begin
      assert (right r0 == c);
      if FStar.IndefiniteDescription.strong_excluded_middle (left r0 == c) then begin
        assert (T.Branch? f0.fsib);
        assert (L.memP c (nboxes f0.fsib))
      end
    end else assert (left r0 == c);
    realizes_framed left right h0 h2 sp f0.fsib fr;
    realizes_framed left right h1 h2 c' u [p];
    assert (realizes left right h2 p s1);
    realizes_plug_framed left right h0 h2 root rest (fill f0 s) s1 fr;
    let in_u (z: B.box a) : Lemma (L.memP z (boxes u) ==> L.memP z sb \/ ~ (mem h0 z)) = () in
    FStar.Classical.forall_intro in_u;
    nboxes_fill f0 f1 u;
    distinct_plug rest s1;
    unshared_intro left right h2 root (plug rest s1);
    bmap_plug view rest s1;
    bmap_plug view rest (fill f0 u);
    replace_bmap view t c u;
    assert (bmap view s1 == bmap view (fill f0 u))
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* `ReplaceNode`                                                                         *)

/// A tree is its left spine closed over its leftmost node, which has no left child.
let rec lmin_plug (#r #a: Type0) (t: nt r a)
  : Lemma (requires T.Branch? t)
          (ensures plug (lspine t) (lmin t) == t /\ all_left (lspine t) /\ T.Branch? (lmin t) /\
                   T.Leaf? (T.left (lmin t)))
          (decreases t)
  = match t with
    | T.Branch l (b, v) rr ->
      if T.Branch? l then begin
        lmin_plug l;
        let f = { went_right = false; fbox = b; fval = v; fsib = rr } in
        plug_append (lspine l) [f] (lmin l);
        let rec al (gs hs: list (fr r a))
          : Lemma (ensures all_left (L.append gs hs) == (all_left gs && all_left hs)) (decreases gs)
          = match gs with [] -> () | _ :: rest -> al rest hs in
        al (lspine l) [f]
      end

/// `ReplaceNode`'s arguments, as boxes of the tree at `root`: what `rpre` says of them.
let rnpre (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root mt pom succ pos: B.box r) : prop =
  unshared left right h root /\
  (let n = nodes view left right h root in
   distinct (nboxes n) /\ all_nonnull n /\ L.memP mt (nboxes n) /\
   (let m = sub n mt in
    T.Branch? m /\ pom == fb (fst (focus n mt)) 0 /\ succ == succ_of m /\
    (T.Branch? (T.right m) ==>
       pos == pos_of m /\
       (let s = lmin (T.right m) in
        (T.Leaf? (T.right s) /\ nred s) \/ (nred (T.right s) /\ not (nred s))))))

/// What `ReplaceNode` leaves: the tree at `root` is `rdel`'s.
let rnpost (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (root0 root1 mt: B.box r) : prop =
  unshared left right h1 root1 /\
  nodes view left right h1 root1 == rdel (nodes view left right h0 root0) mt

let rpre_rnpre (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root mt pom succ pos: B.box r)
  : Lemma (requires unshared left right h root /\
                    rpre c k0 k (nodes view left right h root) mt pom succ pos)
          (ensures rnpre view left right h root mt pom succ pos)
  = ()

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
/// The match's subtree: its box `mt`, and (when it has a right subtree) the left spine `gs`
/// of that subtree down to the successor's subtree `s`.
let m_parts (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root mt pom succ pos: B.box r)
  : Ghost (list (fr r t) & nt r t)
          (requires rnpre view left right h root mt pom succ pos)
          (ensures fun (gs, s) ->
             let n = nodes view left right h root in
             let m = nodes view left right h mt in
             B.is_null mt == false /\ mem h mt /\ unshared left right h mt /\ sub n mt == m /\
             m == T.Branch (nodes view left right h (left (get h mt))) (mt, view mt (get h mt))
                           (nodes view left right h (right (get h mt))) /\
             top (nodes view left right h (left (get h mt))) == left (get h mt) /\
             top (nodes view left right h (right (get h mt))) == right (get h mt) /\
             distinct (nboxes m) /\ all_nonnull m /\
             (forall (y: B.box r). L.memP y (nboxes m) ==> L.memP y (nboxes n)) /\
             (B.is_null pom \/ (mem h pom /\ Cons? (fst (focus n mt)) /\
                                (Cons?.hd (fst (focus n mt))).fbox == pom)) /\
             (B.is_null pom ==> fst (focus n mt) == [] /\ n == m) /\
             (succ == mt <==> T.Leaf? (T.right m)) /\
             (T.Branch? (T.right m) ==>
                T.right m == plug gs s /\ all_left gs /\ gs == lspine (T.right m) /\
                s == lmin (T.right m) /\ T.Branch? s /\ T.Leaf? (T.left s) /\ top s == succ /\
                B.is_null succ == false /\ ~ (succ == mt) /\
                mem h succ /\ unshared left right h succ /\ nodes view left right h succ == s /\
                B.is_null (left (get h succ)) /\
                top (T.right s) == right (get h succ) /\
                unshared left right h (right (get h succ)) /\
                nodes view left right h (right (get h succ)) == T.right s /\
                B.is_null pos == false /\ mem h pos /\ unshared left right h pos /\
                L.memP pos (nboxes m) /\
                (pos == mt <==> gs == []) /\
                (gs == [] ==> right (get h mt) == succ) /\
                (Cons? gs ==> pos == (Cons?.hd gs).fbox /\ left (get h pos) == succ /\
                              ~ (pos == succ) /\ L.memP pos (nboxes (T.right m)))))
  = let n = nodes view left right h root in
    at_box view left right h root mt;
    let m = nodes view left right h mt in
    focus_plug n mt;
    let (fs, _) = focus n mt in
    distinct_plug fs m;
    (match fs with
     | [] -> ()
     | f :: _ -> assert (L.memP f.fbox (nboxes n)); at_box view left right h root f.fbox);
    let T.Branch ml _ mr = m in
    match mr with
    | T.Leaf -> ([], T.Leaf)
    | T.Branch _ _ _ ->
      lmin_plug mr;
      let gs = lspine mr in
      let s = lmin mr in
      let fm = { went_right = true; fbox = mt; fval = view mt (get h mt); fsib = ml } in
      plug_append gs [fm] s;
      assert (m == plug (L.append gs [fm]) s);
      distinct_plug (L.append gs [fm]) s;
      focus_at (L.append gs [fm]) s;
      assert (L.memP (top s) (nboxes mr));
      nodes_sub view left right h mt (top s);
      at_box view left right h mt (top s);
      (match gs with
       | [] -> ()
       | g :: grest ->
         plug_append grest [fm] (fill g s);
         assert (m == plug (L.append grest [fm]) (fill g s));
         distinct_plug (L.append grest [fm]) (fill g s);
         focus_at (L.append grest [fm]) (fill g s);
         assert (L.memP g.fbox (nboxes mr));
         nodes_sub view left right h mt g.fbox;
         at_box view left right h mt g.fbox);
      at_box view left right h root pos;
      (gs, s)
#pop-options

/// The top of `ReplaceNode`: what it reads, and its `Debug.Assert`s.
let rn_start (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root mt pom succ pos: B.box r)
  : Lemma (requires rnpre view left right h root mt pom succ pos)
          (ensures B.is_null mt == false /\ mem h mt /\ unshared left right h mt /\
                   (B.is_null pom \/ mem h pom) /\
                   (succ == mt ==> B.is_null (right (get h mt))) /\
                   (~ (succ == mt) ==>
                      B.is_null succ == false /\ mem h succ /\ unshared left right h succ /\
                      B.is_null pos == false /\ mem h pos /\ ~ (pos == succ) /\
                      B.is_null (left (get h succ)) /\
                      unshared left right h (right (get h succ)) /\
                      (B.is_null (right (get h succ)) == false ==> mem h (right (get h succ))) /\
                      ((B.is_null (right (get h succ)) /\ ST.is_red (tree_of view left right h succ)) \/
                       (ST.is_red (tree_of view left right h (right (get h succ))) /\
                        ~ (ST.is_red (tree_of view left right h succ))))))
  = let _ = m_parts view left right h root mt pom succ pos in
    if FStar.IndefiniteDescription.strong_excluded_middle (succ == mt) then () else begin
      unshared_step left right h succ;
      tree_strip view left right h succ;
      tree_strip view left right h (right (get h succ))
    end

/// `successor = match.Left`, the match having no right subtree.
let rn_a (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root mt pom succ pos: B.box r)
  : Lemma (requires rnpre view left right h root mt pom succ pos /\ succ == mt /\ mem h mt)
          (ensures (let x = left (get h mt) in
                    unshared left right h x /\
                    nodes view left right h x == pre_col (nodes view left right h mt) /\
                    reshaped left right h h mt x /\ (B.is_null x == false ==> mem h x)))
  = let _ = m_parts view left right h root mt pom succ pos in
    unshared_step left right h mt

/// What `successor.Right?.ColorBlack()` writes: the successor's right subtree blackened, or
/// nothing when it is empty.
let rn_black (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (succ: B.box r) : prop =
  mem h0 succ /\
  (let sr = right (get h0 succ) in
   (B.is_null sr ==> h1 == h0) /\
   (B.is_null sr == false ==>
      recolored view left right h0 h1 sr false /\ reshaped left right h0 h1 sr sr /\
      unshared left right h1 sr))

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
/// After `successor.Right?.ColorBlack()`.
let rn_b1 (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (root mt pom succ pos: B.box r)
  : Ghost (list (fr r t) & nt r t)
          (requires rnpre view left right h0 root mt pom succ pos /\ ~ (succ == mt) /\
                    rn_black view left right h0 h1 succ)
          (ensures fun (gs, s) ->
             let m = nodes view left right h0 mt in
             mem h0 mt /\ mem h0 succ /\ mem h0 pos /\
             (let r0 = get h0 mt in
              let sr_top = right (get h0 succ) in
              let sr = T.right s in
              let sr' = recolorn sr false in
              let s1 = T.Branch T.Leaf (succ, view succ (get h0 succ)) sr' in
              T.Branch? (T.right m) /\ gs == lspine (T.right m) /\ s == lmin (T.right m) /\
              T.right m == plug gs s /\ all_left gs /\ T.Branch? s /\ T.Leaf? (T.left s) /\
              s == T.Branch T.Leaf (succ, view succ (get h0 succ)) sr /\
              distinct (nboxes m) /\ all_nonnull m /\
              B.is_null succ == false /\ B.is_null pos == false /\ B.is_null mt == false /\
              (pos == mt <==> gs == []) /\
              (gs == [] ==> right r0 == succ) /\
              (Cons? gs ==> pos == (Cons?.hd gs).fbox /\ left (get h0 pos) == succ /\ ~ (pos == succ)) /\
              L.memP pos (nboxes m) /\ L.memP succ (nboxes (T.right m)) /\
              (B.is_null pom \/ mem h0 pom) /\
              (forall (z: B.box r). L.memP z (nboxes m) ==> mem h0 z) /\
              framed h0 h1 (nboxes sr) /\
              mem h1 mt /\ get h1 mt == r0 /\ mem h1 succ /\ get h1 succ == get h0 succ /\
              mem h1 pos /\ get h1 pos == get h0 pos /\
              unshared left right h1 (left r0) /\ nodes view left right h1 (left r0) == T.left m /\
              boxes (ltree left right h1 (left r0)) == nboxes (T.left m) /\
              unshared left right h1 sr_top /\ nodes view left right h1 sr_top == sr' /\
              (forall (z: B.box r). L.memP z (boxes (ltree left right h1 sr_top)) ==>
                                    L.memP z (nboxes sr) \/ ~ (mem h0 z)) /\
              (Cons? gs ==> unshared left right h1 (right r0) /\
                            nodes view left right h1 (right r0) == plug gs s1)))
  = let (gs, s) = m_parts view left right h0 root mt pom succ pos in
    let m = nodes view left right h0 mt in
    let r0 = get h0 mt in
    let T.Branch ml _ mr = m in
    let sr_top = right (get h0 succ) in
    let T.Branch _ _ sr = s in
    unshared_elim left right h0 mt;
    let in_m (z: B.box r) : Lemma (L.memP z (nboxes m) ==> mem h0 z) =
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (nboxes m))
      then realizes_mem left right h0 mt (ltree left right h0 mt) z in
    FStar.Classical.forall_intro in_m;
    let fm = { went_right = true; fbox = mt; fval = view mt r0; fsib = ml } in
    plug_append gs [fm] s;
    distinct_plug (L.append gs [fm]) s;
    assert (~ (L.memP mt (nboxes sr)) /\ ~ (L.memP succ (nboxes sr)) /\ ~ (L.memP pos (nboxes sr)));
    if B.is_null sr_top then begin
      assert (sr == T.Leaf);
      (gs, s)
    end else begin
      assert (nodes view left right h0 sr_top == sr);
      let lsr = ltree left right h0 sr_top in
      assert (nboxes sr == boxes lsr);
      framed_outside left right h0 h1 (boxes lsr) (left r0);
      (match gs with
       | [] -> ()
       | g :: _ ->
         let fs_ = { went_right = true; fbox = succ; fval = view succ (get h0 succ); fsib = T.Leaf } in
         assert (fill fs_ sr == s);
         distinct_plug (fs_ :: gs) sr;
         focus_at (fs_ :: gs) sr;
         assert (L.memP sr_top (nboxes mr));
         graft_at view left right h0 h1 (right r0) sr_top);
      (gs, s)
    end
#pop-options

/// The writes of `ReplaceNode`'s second arm, after `successor.Right?.ColorBlack()` (`h1`):
/// when the successor is not the match's right child, `parentOfSuccessor.Left =
/// successor.Right` and `successor.Right = match.Right`; then `successor.Left = match.Left`.
let rn_writes (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h1 h4: heap r) (mt succ pos: B.box r) : prop =
  mem h1 succ /\ mem h1 mt /\ mem h1 pos /\ mem h4 succ /\
  left (get h4 succ) == left (get h1 mt) /\
  view succ (get h4 succ) == view succ (get h1 succ) /\
  (pos == mt ==> right (get h4 succ) == right (get h1 succ) /\ framed h1 h4 [succ]) /\
  (~ (pos == mt) ==>
     right (get h4 succ) == right (get h1 mt) /\ mem h4 pos /\
     left (get h4 pos) == right (get h1 succ) /\ right (get h4 pos) == right (get h1 pos) /\
     view pos (get h4 pos) == view pos (get h1 pos) /\ framed h1 h4 [succ; pos])

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
/// `rn_writes` from `ReplaceNode`'s three writes, when `parentOfSuccessor != match`.
let rn_writes_ne (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h1: heap r) (mt succ pos: B.box r) (vp vs1 vs2: r)
  : Lemma (requires mem h1 succ /\ mem h1 mt /\ mem h1 pos /\
                    ~ (pos == mt) /\ ~ (pos == succ) /\ ~ (succ == mt) /\
                    left vp == right (get h1 succ) /\ right vp == right (get h1 pos) /\
                    view pos vp == view pos (get h1 pos) /\
                    left vs2 == left (get h1 mt) /\ right vs2 == right (get h1 mt) /\
                    view succ vs2 == view succ (get h1 succ))
          (ensures rn_writes view left right h1 (upd (upd (upd h1 pos vp) succ vs1) succ vs2) mt succ pos)
          [SMTPat (rn_writes view left right h1 (upd (upd (upd h1 pos vp) succ vs1) succ vs2) mt succ pos)]
  = let h2 = upd h1 pos vp in
    let h3 = upd h2 succ vs1 in
    let h4 = upd h3 succ vs2 in
    lookup_upd h1 pos succ vp; lookup_upd h2 succ succ vs1; lookup_upd h3 succ succ vs2;
    lookup_upd h1 pos pos vp; lookup_upd h2 succ pos vs1; lookup_upd h3 succ pos vs2;
    assert (mem h4 succ /\ get h4 succ == vs2);
    assert (mem h4 pos /\ get h4 pos == vp);
    assert (framed h1 h4 [succ; pos])

/// `rn_writes` when `parentOfSuccessor == match`: only `successor.Left` is written.
let rn_writes_eq (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h1: heap r) (mt succ pos: B.box r) (vs: r)
  : Lemma (requires mem h1 succ /\ mem h1 mt /\ pos == mt /\ ~ (succ == mt) /\
                    left vs == left (get h1 mt) /\ right vs == right (get h1 succ) /\
                    view succ vs == view succ (get h1 succ))
          (ensures rn_writes view left right h1 (upd h1 succ vs) mt succ pos)
          [SMTPat (rn_writes view left right h1 (upd h1 succ vs) mt succ pos)]
  = let h4 = upd h1 succ vs in
    lookup_upd h1 succ succ vs;
    assert (mem h4 succ /\ get h4 succ == vs);
    assert (framed h1 h4 [succ])
#pop-options

/// What the second arm leaves at the successor: `pre_col` of the match's subtree.
let rn_b_post (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h4: heap r) (mt pom succ: B.box r) : prop =
  unshared left right h4 succ /\ nodes view left right h4 succ == pre_col (nodes view left right h0 mt) /\
  reshaped left right h0 h4 mt succ /\ mem h0 mt /\ mem h4 mt /\ get h4 mt == get h0 mt /\
  (B.is_null pom \/ mem h4 pom)

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let rn_b_eq (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1 h4: heap r) (root mt pom succ pos: B.box r)
  : Lemma (requires rnpre view left right h0 root mt pom succ pos /\ ~ (succ == mt) /\
                    rn_black view left right h0 h1 succ /\ rn_writes view left right h1 h4 mt succ pos /\
                    pos == mt)
          (ensures rn_b_post view left right h0 h4 mt pom succ)
  = let (gs, s) = rn_b1 view left right h0 h1 root mt pom succ pos in
    let m = nodes view left right h0 mt in
    let r0 = get h0 mt in
    let sr_top = right (get h0 succ) in
    link2_nodes view left right h1 h4 succ (left r0) sr_top;
    lmin_plug (T.right m);
    assert (nodes view left right h4 succ == pre_col m);
    unshared_elim left right h0 mt;
    nboxes_boxes (ltree left right h0 mt);
    assert (framed h0 h4 (boxes (ltree left right h0 mt)))

let rn_b_ne (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1 h4: heap r) (root mt pom succ pos: B.box r)
  : Lemma (requires rnpre view left right h0 root mt pom succ pos /\ ~ (succ == mt) /\
                    rn_black view left right h0 h1 succ /\ rn_writes view left right h1 h4 mt succ pos /\
                    ~ (pos == mt))
          (ensures rn_b_post view left right h0 h4 mt pom succ)
  = let (gs, s) = rn_b1 view left right h0 h1 root mt pom succ pos in
    let m = nodes view left right h0 mt in
    let r0 = get h0 mt in
    let sr_top = right (get h0 succ) in
    let T.Branch _ (_, sv) sr = s in
    let sr' = recolorn sr false in
    let s1 = T.Branch T.Leaf (succ, sv) sr' in
    let mr_top = right r0 in
    let h2 = upd h1 pos (get h4 pos) in
    assert (relinked view left right h1 h2 pos succ sr_top);
    distinct_plug gs s1;
    focus_at gs s1;
    distinct_plug gs sr';
    relink_nodes view left right h1 h2 mr_top succ sr_top;
    assert (nodes view left right h2 mr_top == plug gs sr');
    assert (framed h2 h4 [succ]);
    framed_outside left right h1 h2 [pos] (left r0);
    let mr2 = plug gs sr' in
    let in_mr2 (z: B.box r)
      : Lemma (L.memP z (nboxes mr2) ==> (L.memP z (fboxes gs) \/ L.memP z (nboxes sr) \/ ~ (mem h0 z))) =
      mem_plug z gs sr' in
    FStar.Classical.forall_intro in_mr2;
    link2_nodes view left right h2 h4 succ (left r0) mr_top;
    lmin_plug (T.right m);
    assert (nodes view left right h4 succ == pre_col m);
    unshared_elim left right h0 mt;
    nboxes_boxes (ltree left right h0 mt);
    assert (framed h0 h4 (boxes (ltree left right h0 mt)))
#pop-options

/// The end of `ReplaceNode`'s second arm.
let rn_b (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1 h4: heap r) (root mt pom succ pos: B.box r)
  : Lemma (requires rnpre view left right h0 root mt pom succ pos /\ ~ (succ == mt) /\
                    rn_black view left right h0 h1 succ /\ rn_writes view left right h1 h4 mt succ pos)
          (ensures rn_b_post view left right h0 h4 mt pom succ)
  = if FStar.IndefiniteDescription.strong_excluded_middle (pos == mt)
    then rn_b_eq view left right h0 h1 h4 root mt pom succ pos
    else rn_b_ne view left right h0 h1 h4 root mt pom succ pos

/// `successor?.Color = match.Color`.
let rn_color (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h4 h5: heap r) (mt x: B.box r) : prop =
  (B.is_null x ==> h5 == h4) /\
  (B.is_null x == false ==>
     mem h4 x /\ mem h4 mt /\ mem h5 x /\
     left (get h5 x) == left (get h4 x) /\ right (get h5 x) == right (get h4 x) /\
     view x (get h5 x) == (fst (view x (get h4 x)), snd (view mt (get h4 mt))) /\
     framed h4 h5 [x])

/// `rn_color` from the colour write.
let rn_color_upd (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h4: heap r) (mt x: B.box r) (v: r)
  : Lemma (requires B.is_null x == false /\ mem h4 x /\ mem h4 mt /\
                    left v == left (get h4 x) /\ right v == right (get h4 x) /\
                    view x v == (fst (view x (get h4 x)), snd (view mt (get h4 mt))))
          (ensures rn_color view left right h4 (upd h4 x v) mt x)
          [SMTPat (rn_color view left right h4 (upd h4 x v) mt x)]
  = let h5 = upd h4 x v in
    lookup_upd h4 x x v;
    assert (mem h5 x /\ get h5 x == v);
    assert (framed h4 h5 [x])

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
/// The end of `ReplaceNode`: the colour copied, and `ReplaceChildOrRoot(parentOfMatch, match,
/// successor)`.
let rn_done (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h4 h5 h6: heap r) (root0 root6 mt pom succ pos x: B.box r)
  : Lemma (requires rnpre view left right h0 root0 mt pom succ pos /\
                    unshared left right h4 x /\
                    nodes view left right h4 x == pre_col (nodes view left right h0 mt) /\
                    reshaped left right h0 h4 mt x /\
                    mem h0 mt /\ mem h4 mt /\ get h4 mt == get h0 mt /\
                    rn_color view left right h4 h5 mt x /\
                    replaced view left right h5 h6 root0 root6 pom mt x)
          (ensures rnpost view left right h0 h6 root0 root6 mt)
  = let _ = m_parts view left right h0 root0 mt pom succ pos in
    let n = nodes view left right h0 root0 in
    let m = nodes view left right h0 mt in
    let u = recolorn (pre_col m) (nred m) in
    if B.is_null x then begin
      assert (nodes view left right h5 x == u);
      assert (reshaped left right h0 h5 mt x)
    end else begin
      let vx = get h4 x in
      unshared_step left right h4 x;
      nodes_step view left right h4 x;
      link2_nodes view left right h4 h5 x (left vx) (right vx);
      assert (nodes view left right h5 x == u);
      assert (reshaped left right h4 h5 x x);
      assert (reshaped left right h0 h5 mt x)
    end;
    if B.is_null pom then ()
    else begin
      let lt = ltree left right h0 root0 in
      focus_bmap view lt mt;
      assert (Cons? (fst (focus lt mt)));
      assert ((Cons?.hd (fst (focus lt mt))).fbox == pom);
      relink_away view left right h0 h5 h6 root0 mt x
    end
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* After the loop                                                                        *)

/// No match: nothing is removed.
let r_none (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root: B.box r)
  : Lemma (requires S.key_index c k0 k < 0 /\ unshared left right h root /\
                    ok c k0 (nodes view left right h root))
          (ensures okp view left right c (removed c k0 k) h root)
  = ()

/// After `ReplaceNode`: the tree is a set of the remaining keys.
let r_replaced (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h0 h1: heap r) (root0 root1 mt pom succ pos: B.box r)
  : Lemma (requires rpre c k0 k (nodes view left right h0 root0) mt pom succ pos /\
                    rnpost view left right h0 h1 root0 root1 mt)
          (ensures okp view left right c (removed c k0 k) h1 root1)
  = ()

/// The removal takes one key away when there is one to take.
let removed_length (#t: Type0) (c: O.comparer t) (k0: Seq.seq t) (k: t)
  : Lemma (ensures Seq.length (removed c k0 k) ==
                   (if S.key_index c k0 k >= 0 then Seq.length k0 - 1 else Seq.length k0))
          [SMTPat (Seq.length (removed c k0 k))]
  = ()

/// `root?.ColorBlack()` at the end: also when the tree is now empty.
let r_finish (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k1: Seq.seq t) (h0 h1: heap r) (root: B.box r)
  : Lemma (requires okp view left right c k1 h0 root /\
                    (B.is_null root ==> h1 == h0) /\
                    (B.is_null root == false ==> recolored view left right h0 h1 root false))
          (ensures ST.keys (tree_of view left right h1 root) == k1 /\
                   S.strictly_sorted c k1 /\
                   ST.red_black (tree_of view left right h1 root) /\
                   T.size (tree_of view left right h1 root) == Seq.length k1)
  = if B.is_null root then begin
      unshared_elim left right h0 root;
      Pulse.Lib.CSharp.TopDown.finish c k1 (nodes view left right h0 root);
      tree_strip view left right h1 root;
      ST.keys_length (tree_of view left right h1 root)
    end else finish view left right c k1 h0 h1 root

/// `ReplaceNode`'s call, at the heap: `rpre` of the tree at `root`.
let rpreh (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root mt pom succ pos: B.box r) : prop =
  unshared left right h root /\ rpre c k0 k (nodes view left right h root) mt pom succ pos

/// After the loop: no match and nothing to remove, or `ReplaceNode` can be called.
let r_after (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root par gp mt pom: B.box r)
    (found: bool)
  : Lemma (requires rinvh view left right c k0 k h root B.null par gp mt pom found)
          (ensures (B.is_null mt ==> found == false /\ S.key_index c k0 k < 0 /\
                                     okp view left right c (removed c k0 k) h root) /\
                   (B.is_null mt == false ==>
                      found == true /\ S.key_index c k0 k >= 0 /\
                      rpreh view left right c k0 k h root mt pom par gp /\
                      rnpre view left right h root mt pom par gp))
  = r_at_end view left right c k0 k h root par gp mt pom found;
    if B.is_null mt then r_none view left right c k0 k h root
    else rpre_rnpre view left right c k0 k h root mt pom par gp
