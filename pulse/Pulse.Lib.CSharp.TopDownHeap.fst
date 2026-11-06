module Pulse.Lib.CSharp.TopDownHeap

/// R27.26. `SortedSet<T>.AddIfNotPresent`'s top-down insertion over the heap of a region:
/// `TopDown`'s descent, read through `nodes` (the tree of boxes and views a pointer reaches).
/// Every definition takes the region class's view and links first (`[RegionOp]`, R27.22),
/// then the arguments the C# side passes. The props are what `Node`'s helpers ensure and
/// what the loop carries; the lemmas are ghost steps the C# code calls.
///
/// Nothing here is trusted beyond `Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8).

open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
open Pulse.Lib.CSharp.RegionPath
open Pulse.Lib.CSharp.TopDown
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq

(* ------------------------------------------------------------------------------------ *)
(* What `Node`'s helpers do to the boxes                                                 *)

/// `ColorBlack`/`ColorRed`: the node's colour set, every box where it was.
let recolored (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x: B.box r) (red: bool) : prop =
  nodes view left right h1 x == recolorn (nodes view left right h0 x) red

/// `Split4Node`.
let split4ed (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x: B.box r) : prop =
  nodes view left right h1 x == split4n (nodes view left right h0 x)

/// `RotateLeft` (`w0`, `w1` both true), `RotateRight` (both false), `RotateLeftRight`
/// (true, false) and `RotateRightLeft` (false, true), from `x` to the new top `y`.
let rotated (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (x y: B.box r) (w0 w1: bool) : prop =
  nodes view left right h1 y == rot_for w0 w1 (nodes view left right h0 x)

(* ------------------------------------------------------------------------------------ *)
(* The descent                                                                           *)

/// The child of `x` the search goes on to after comparing to `o`, or null.
let toward (#r: Type0) (left right: r -> B.box r) (h: heap r) (x: B.box r) (o: int) : B.box r =
  match lookup h x with
  | Some v -> if o < 0 then left v else right v
  | None -> B.null

/// The loop invariant: the tree at `root` is a set of `k0`'s keys, red-black but for its
/// root, and the path from `root` to `cur` is a valid 2-3-4 descent for `k`.
let inv (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp ggp: B.box r) (o: int)
  : prop =
  unshared left right h root /\ T.Branch? (nodes view left right h root) /\
  ok c k0 (nodes view left right h root) /\ descent c k (nodes view left right h root) cur par gp ggp o

/// The loop's measure.
let measure (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k: t) (h: heap r) (root cur: B.box r) : GTot int =
  meas c k (sub (nodes view left right h root) cur)

/// The end of an iteration, before `current` moves down: the invariant at `cur`'s next
/// node, which has a smaller measure than `m0`.
let ready (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp: B.box r) (o: int)
    (m0: int) : prop =
  mem h cur /\
  inv view left right c k0 k h root (toward left right h cur o) cur par gp o /\
  measure view left right c k h root (toward left right h cur o) < m0

/// `IsNonNullRed(par)`.
let par_red (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (par: B.box r) : prop =
  B.is_null par == false /\ mem h par /\ ST.is_red (tree_of view left right h par)

/// `InsertionBalance(cur, ref par, gp, ggp)`'s precondition.
let balance_pre (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root cur par gp ggp: B.box r) : prop =
  unshared left right h root /\ balance_ready (nodes view left right h root) cur par gp ggp

/// `InsertionBalance`'s postcondition: the tree is `balance`d, now at `root1`, and `par1`
/// is `cur`'s parent in it.
let balanced (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (root0 root1 cur par0 par1 ggp: B.box r) : prop =
  unshared left right h1 root1 /\
  nodes view left right h1 root1 == balance (nodes view left right h0 root0) cur /\
  par1 == (if same_side (nodes view left right h0 root0) cur then par0 else ggp)

/// After a split under a red parent: `InsertionBalance`'s precondition, and what its
/// postcondition will give.
let pending (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp ggp: B.box r) (o: int)
    (m0: int) : prop =
  balance_pre view left right h root cur par gp ggp /\
  (let n2 = balance (nodes view left right h root) cur in
   let par2 = if same_side (nodes view left right h root) cur then par else ggp in
   ok c k0 n2 /\ T.Branch? n2 /\ descent c k n2 (next c k n2 cur) cur par2 gp o /\
   meas c k (sub n2 (next c k n2 cur)) < m0 /\
   L.memP cur (nboxes n2) /\ o == cmp c k (nkey (sub n2 cur) k))

(* ------------------------------------------------------------------------------------ *)
(* Facts of the heap                                                                     *)

let tree_strip (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (x: B.box r)
  : Lemma (ensures tree_of view left right h x == strip (nodes view left right h x))
  = ()

/// A box of the tree at `root`: the subtree there is the tree at it.
let at_box (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root x: B.box r)
  : Lemma (requires unshared left right h root /\ L.memP x (nboxes (nodes view left right h root)) /\
                    B.is_null x == false)
          (ensures mem h x /\ unshared left right h x /\ wf left right h x /\
                   sub (nodes view left right h root) x == nodes view left right h x /\
                   (let v = get h x in
                    nodes view left right h x ==
                      T.Branch (nodes view left right h (left v)) (x, view x v) (nodes view left right h (right v)) /\
                    top (nodes view left right h (left v)) == left v /\
                    top (nodes view left right h (right v)) == right v))
  = nodes_sub view left right h root x;
    nodes_step view left right h x;
    unshared_wf left right h x

/// The next node in heap terms.
let next_toward (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k: t) (h: heap r) (root x: B.box r) (o: int)
  : Lemma (requires unshared left right h root /\ L.memP x (nboxes (nodes view left right h root)) /\
                    B.is_null x == false /\
                    o == cmp c k (nkey (sub (nodes view left right h root) x) k))
          (ensures mem h x /\ next c k (nodes view left right h root) x == toward left right h x o)
  = at_box view left right h root x

/// Where the descent is at a non-null `cur`.
let descent_at (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp ggp: B.box r) (o: int)
  : Lemma (requires inv view left right c k0 k h root cur par gp ggp o /\ B.is_null cur == false)
          (ensures L.memP cur (nboxes (nodes view left right h root)))
  = let n = nodes view left right h root in
    let (fs, s) = descent_elim c k n cur par gp ggp o in
    match s with
    | T.Branch _ _ _ -> ok_focus c k0 fs s
    | T.Leaf -> ()

(* ------------------------------------------------------------------------------------ *)
(* The steps                                                                             *)

/// Before the loop: the tree at a non-null `root` is the set's.
let start (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root: B.box r)
  : Lemma (requires unshared left right h root /\ B.is_null root == false /\
                    ST.keys (tree_of view left right h root) == k0 /\ S.strictly_sorted c k0 /\
                    ST.red_black (tree_of view left right h root))
          (ensures inv view left right c k0 k h root root B.null B.null B.null 0)
  = let lt = ltree left right h root in
    let n = nodes view left right h root in
    unshared_elim left right h root;
    nboxes_boxes lt;
    let nn (y: B.box r) : Lemma (L.memP y (nboxes n) ==> B.is_null y == false) =
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (nboxes n))
      then realizes_nonnull left right h root lt y in
    FStar.Classical.forall_intro nn;
    nodes_step view left right h root;
    top_ltree left right h root;
    descent_root c k n

/// The top of an iteration: `cur` is a node of the tree, so its fields can be read.
let at_cur (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp ggp: B.box r) (o: int)
  : Lemma (requires inv view left right c k0 k h root cur par gp ggp o /\ B.is_null cur == false)
          (ensures mem h cur /\ unshared left right h cur /\ wf left right h cur)
  = descent_at view left right c k0 k h root cur par gp ggp o;
    at_box view left right h root cur

/// After `order = comparer.Compare(item, current.Item)`: `order == 0` means the key is in
/// the set; otherwise, without a split, the iteration is done.
let look (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root cur par gp ggp: B.box r)
    (o0 o: int)
  : Lemma (requires inv view left right c k0 k h root cur par gp ggp o0 /\ B.is_null cur == false /\
                    mem h cur /\ o == cmp c k (fst (view cur (get h cur))))
          (ensures (o == 0 ==> S.key_index c k0 k >= 0) /\
                   (o <> 0 /\
                    not (ST.is_red (T.left (tree_of view left right h cur)) &&
                         ST.is_red (T.right (tree_of view left right h cur))) ==>
                    ready view left right c k0 k h root cur par gp o
                      (measure view left right c k h root cur)))
  = let n = nodes view left right h root in
    descent_at view left right c k0 k h root cur par gp ggp o0;
    at_box view left right h root cur;
    let v = get h cur in
    at_box view left right h root cur;
    assert (nkey (sub n cur) k == fst (view cur v));
    if o = 0 then found c k0 k n cur par gp ggp o0
    else begin
      let l = nodes view left right h (left v) in
      let rr = nodes view left right h (right v) in
      tree_strip view left right h cur;
      assert (strip (sub n cur) == tree_of view left right h cur);
      assert (is4 (sub n cur) == (nred l && nred rr));
      if is4 (sub n cur) then ()
      else begin
        step_plain c k0 k n cur par gp ggp o0 o;
        meas_plain c k0 k n cur par gp ggp o0 o;
        next_toward view left right c k h root cur o
      end
    end

/// The end of the method: `root.ColorBlack()` leaves the set's tree.
let finish (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (h0 h1: heap r) (root: B.box r)
  : Lemma (requires unshared left right h0 root /\ ok c k0 (nodes view left right h0 root) /\
                    recolored view left right h0 h1 root false)
          (ensures ST.keys (tree_of view left right h1 root) == k0 /\
                   ST.red_black (tree_of view left right h1 root) /\
                   T.size (tree_of view left right h1 root) == Seq.length k0)
  = Pulse.Lib.CSharp.TopDown.finish c k0 (nodes view left right h0 root);
    tree_strip view left right h1 root;
    ST.keys_length (tree_of view left right h1 root)

(* ------------------------------------------------------------------------------------ *)
(* Writes that keep the links                                                            *)

/// A write at `x` that keeps its links: what `x` reaches is the same tree but for `x`'s view.
let nodes_upd (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (x: B.box r) (v: r)
  : Lemma (requires unshared left right h x /\ B.is_null x == false /\ mem h x /\
                    left v == left (get h x) /\ right v == right (get h x))
          (ensures unshared left right (upd h x v) x /\
                   nodes view left right (upd h x v) x ==
                     T.Branch (nodes view left right h (left v)) (x, view x v)
                              (nodes view left right h (right v)))
          [SMTPat (nodes view left right (upd h x v) x)]
  = unshared_step left right h x

/// What `x` reaches, one level down.
let nodes_at (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (x: B.box r)
  : Lemma (requires unshared left right h x /\ B.is_null x == false)
          (ensures mem h x /\
                   nodes view left right h x ==
                     T.Branch (nodes view left right h (left (get h x))) (x, view x (get h x))
                              (nodes view left right h (right (get h x))))
          [SMTPat (nodes view left right h x); SMTPat (unshared left right h x)]
  = nodes_step view left right h x

/// A re-linking inside the tree at `y` (`x` among its boxes) seen from `y`.
let graft_at (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (y x: B.box r)
  : Lemma (requires unshared left right h0 y /\ L.memP x (nboxes (nodes view left right h0 y)) /\
                    reshaped left right h0 h1 x x /\ unshared left right h1 x)
          (ensures unshared left right h1 y /\ reshaped left right h0 h1 y y /\
                   nodes view left right h1 y ==
                     replace (nodes view left right h0 y) x (nodes view left right h1 x))
  = let lt = ltree left right h1 x in
    unshared_elim left right h1 x;
    nboxes_boxes lt;
    if B.is_null x then begin
      nboxes_boxes (ltree left right h0 y);
      unshared_elim left right h0 y;
      realizes_nonnull left right h0 y (ltree left right h0 y) x
    end else begin
      top_ltree left right h1 x;
      unshared_mem left right h1 x;
      unshared_step left right h1 x;
      graft_nodes view left right h0 h1 y x x
    end

(* ------------------------------------------------------------------------------------ *)
(* Splitting                                                                             *)

/// Whether `par` is a red node, read off the tree at `root` holding it (or `par` null).
let par_red_at (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root par: B.box r)
  : Lemma (requires unshared left right h root /\ distinct (nboxes (nodes view left right h root)) /\
                    all_nonnull (nodes view left right h root) /\
                    (B.is_null par \/ L.memP par (nboxes (nodes view left right h root))))
          (ensures (par_red view left right h par <==> nred (sub (nodes view left right h root) par)))
  = let n = nodes view left right h root in
    if B.is_null par then sub_absent n par
    else begin
      at_box view left right h root par;
      tree_strip view left right h par
    end

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
/// After `current.Split4Node()`: with a black parent the iteration is done; with a red one,
/// `InsertionBalance` is due.
let split (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h1: heap r) (root cur par gp ggp: B.box r)
    (o0 o: int)
  : Lemma (requires inv view left right c k0 k h root cur par gp ggp o0 /\ B.is_null cur == false /\
                    mem h cur /\ o == cmp c k (fst (view cur (get h cur))) /\ o <> 0 /\
                    ST.is_red (T.left (tree_of view left right h cur)) /\
                    ST.is_red (T.right (tree_of view left right h cur)) /\
                    reshaped left right h h1 cur cur /\ unshared left right h1 cur /\
                    split4ed view left right h h1 cur)
          (ensures unshared left right h1 root /\ mem h1 cur /\
                   (B.is_null par == false ==> mem h1 par) /\
                   (~ (par_red view left right h1 par) ==>
                      ready view left right c k0 k h1 root cur par gp o
                        (measure view left right c k h root cur)) /\
                   (par_red view left right h1 par ==>
                      pending view left right c k0 k h1 root cur par gp ggp o
                        (measure view left right c k h root cur)))
  = let n = nodes view left right h root in
    descent_at view left right c k0 k h root cur par gp ggp o0;
    at_box view left right h root cur;
    let v = get h cur in
    assert (nkey (sub n cur) k == fst (view cur v));
    tree_strip view left right h cur;
    assert (is4 (sub n cur));
    step_split c k0 k n cur par gp ggp o0 o;
    meas_step_split c k0 k n cur par gp ggp o0 o;
    let s1 = split4n (sub n cur) in
    assert (nodes view left right h1 cur == s1);
    nboxes_boxes (ltree left right h1 cur);
    graft_nodes view left right h h1 root cur cur;
    let n1 = nodes view left right h1 root in
    assert (n1 == replace n cur s1);
    focus_plug n cur;
    let (fs, s) = focus n cur in
    let same (y: B.box r) : Lemma (L.memP y (nboxes n1) <==> L.memP y (nboxes n)) =
      mem_plug y fs s; mem_plug y fs s1 in
    FStar.Classical.forall_intro same;
    (if B.is_null par then () else (descent_next c k0 k n cur par gp ggp o0; at_box view left right h1 root par));
    if nred (sub n1 par) then begin
      par_red_at view left right h1 root par;
      let n2 = balance n1 cur in
      descent_next c k0 k n2 (next c k n2 cur) cur
        (if same_side n1 cur then par else ggp) gp o
    end else begin
      par_red_at view left right h1 root par;
      descent_next c k0 k n1 (next c k n1 cur) cur par gp o;
      next_toward view left right c k h1 root cur o
    end
#pop-options

/// After `InsertionBalance`: the iteration is done.
let after_balance (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h2: heap r) (root root2 cur par par2 gp ggp: B.box r)
    (o m0: int)
  : Lemma (requires pending view left right c k0 k h root cur par gp ggp o m0 /\
                    balanced view left right h h2 root root2 cur par par2 ggp)
          (ensures ready view left right c k0 k h2 root2 cur par2 gp o m0)
  = next_toward view left right c k h2 root2 cur o;
    at_box view left right h2 root2 cur

(* ------------------------------------------------------------------------------------ *)
(* InsertionBalance                                                                      *)

/// The sides the search took at the parent (`w0`) and the grandparent (`w1`) of `cur`.
let bal_sides (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root cur: B.box r) (w0 w1: bool) : prop =
  match fst (focus (nodes view left right h root) cur) with
  | f0 :: f1 :: _ -> w0 == f0.went_right /\ w1 == f1.went_right
  | _ -> False

/// The parent and grandparent are nodes of the tree, so `InsertionBalance` can read them.
let bal_start (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root cur par gp ggp: B.box r)
  : Lemma (requires balance_pre view left right h root cur par gp ggp)
          (ensures mem h par /\ mem h gp /\ wf left right h par /\ wf left right h gp /\
                   unshared left right h gp /\ B.is_null par == false /\ B.is_null gp == false)
  = let n = nodes view left right h root in
    focus_plug n cur;
    let (f0 :: f1 :: rest, s) = focus n cur in
    mem_plug par (f0 :: f1 :: rest) s;
    mem_plug gp (f0 :: f1 :: rest) s;
    at_box view left right h root par;
    at_box view left right h root gp

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
/// What the comparisons `grandParent.Right == parent` (`w1`) and `parent.Right == current`
/// (`w0`) tell: the sides, and that the rotation they choose applies.
let bal_rot (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root cur par gp ggp: B.box r) (w0 w1: bool)
  : Lemma (requires balance_pre view left right h root cur par gp ggp /\ mem h par /\ mem h gp /\
                    (w1 <==> right (get h gp) == par) /\ (w0 <==> right (get h par) == cur))
          (ensures bal_sides view left right h root cur w0 w1 /\
                   (let tg = tree_of view left right h gp in
                    (w0 && w1 ==> ~ (T.Leaf? (T.right tg))) /\
                    (not w0 && not w1 ==> ~ (T.Leaf? (T.left tg))) /\
                    (w0 && not w1 ==> ~ (T.Leaf? (T.left tg)) /\ ~ (T.Leaf? (T.right (T.left tg)))) /\
                    (not w0 && w1 ==> ~ (T.Leaf? (T.right tg)) /\ ~ (T.Leaf? (T.left (T.right tg))))))
  = let n = nodes view left right h root in
    focus_plug n cur;
    let (f0 :: f1 :: rest, s) = focus n cur in
    let tp = fill f0 s in
    let tgn = fill f1 tp in
    distinct_plug (f0 :: f1 :: rest) s;
    distinct_plug rest tgn;
    focus_at rest tgn;
    focus_at (f1 :: rest) tp;
    at_box view left right h root gp;
    at_box view left right h root par;
    assert (nodes view left right h gp == tgn);
    assert (nodes view left right h par == tp);
    mem_box_nboxes cur s;
    assert (B.is_null cur == false);
    mem_box_nboxes par f1.fsib;
    mem_box_nboxes cur f0.fsib;
    tree_strip view left right h gp
#pop-options

#push-options "--z3rlimit 60 --fuel 4 --ifuel 2"
/// `InsertionBalance`'s rotation keeps the grandparent's boxes.
let rot_boxes (#r #a: Type0) (f0 f1: fr r a) (s: nt r a) (y: B.box r)
  : Lemma (requires T.Branch? s)
          (ensures L.memP y (nboxes (rot_for f0.went_right f1.went_right (fill f1 (fill f0 s)))) <==>
                   L.memP y (nboxes (fill f1 (fill f0 s))))
  = let T.Branch sa (sc, sv) sb = s in
    let p = f0.fbox in let g = f1.fbox in
    let ps = f0.fsib in let u = f1.fsib in
    match f0.went_right, f1.went_right with
    | false, false ->
      assert (rot_for false false (fill f1 (fill f0 s)) ==
              T.Branch s (p, f0.fval) (T.Branch ps (g, f1.fval) u))
    | true, true ->
      assert (rot_for true true (fill f1 (fill f0 s)) ==
              T.Branch (T.Branch u (g, f1.fval) ps) (p, f0.fval) s)
    | true, false ->
      assert (rot_for true false (fill f1 (fill f0 s)) ==
              T.Branch (T.Branch ps (p, f0.fval) sa) (sc, sv) (T.Branch sb (g, f1.fval) u))
    | false, true ->
      assert (rot_for false true (fill f1 (fill f0 s)) ==
              T.Branch (T.Branch u (g, f1.fval) sa) (sc, sv) (T.Branch sb (p, f0.fval) ps))
#pop-options

/// The grandparent's subtree, seen from the tree at `root`.
let bal_focus (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root cur par gp ggp: B.box r)
  : Ghost (fr r t & fr r t & list (fr r t) & nt r t)
          (requires balance_pre view left right h root cur par gp ggp)
          (ensures fun (f0, f1, rest, s) ->
             let n = nodes view left right h root in
             let tg = fill f1 (fill f0 s) in
             fst (focus n cur) == f0 :: f1 :: rest /\ n == plug rest tg /\ T.Branch? s /\
             f0.fbox == par /\ f1.fbox == gp /\ fb rest 0 == ggp /\
             nodes view left right h gp == tg /\ top tg == gp /\ fst (focus n gp) == rest /\
             sub n gp == tg /\ L.memP gp (nboxes n) /\ distinct (nboxes n) /\
             balance n cur == replace n gp (balance_sub f0.went_right f1.went_right tg))
  = let n = nodes view left right h root in
    focus_plug n cur;
    let (f0 :: f1 :: rest, s) = focus n cur in
    let tg = fill f1 (fill f0 s) in
    distinct_plug (f0 :: f1 :: rest) s;
    distinct_plug rest tg;
    focus_at rest tg;
    at_box view left right h root gp;
    (match s with T.Leaf -> assert (B.is_null cur == false) | _ -> ());
    (f0, f1, rest, s)

/// The great-grandparent, if any, is a node of the tree, so it can be re-linked.
let bal_ggp (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root cur par gp ggp: B.box r)
  : Lemma (requires balance_pre view left right h root cur par gp ggp)
          (ensures B.is_null ggp \/ mem h ggp)
  = let (f0, f1, rest, s) = bal_focus view left right h root cur par gp ggp in
    match rest with
    | [] -> ()
    | f :: _ ->
      assert (L.memP f.fbox (nboxes (nodes view left right h root)));
      if B.is_null ggp then () else at_box view left right h root ggp

/// After the rotation, before `grandParent.ColorRed()`.
let bal_mid (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (root cur par gp ggp y: B.box r) (w0 w1: bool)
  : Lemma (requires balance_pre view left right h0 root cur par gp ggp /\
                    bal_sides view left right h0 root cur w0 w1 /\
                    rotated view left right h0 h1 gp y w0 w1 /\ unshared left right h1 y)
          (ensures unshared left right h1 gp /\ L.memP gp (nboxes (nodes view left right h1 y)))
  = let (f0, f1, rest, s) = bal_focus view left right h0 root cur par gp ggp in
    rot_boxes f0 f1 s gp;
    nodes_sub view left right h1 y gp

/// After `grandParent.ColorRed()`, before `newChildOfGreatGrandParent.ColorBlack()`.
let bal_red (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1 h2: heap r) (root cur par gp ggp y: B.box r) (w0 w1: bool)
  : Lemma (requires balance_pre view left right h0 root cur par gp ggp /\
                    bal_sides view left right h0 root cur w0 w1 /\
                    rotated view left right h0 h1 gp y w0 w1 /\
                    reshaped left right h0 h1 gp y /\ unshared left right h1 y /\
                    recolored view left right h1 h2 gp true /\
                    reshaped left right h1 h2 gp gp /\ unshared left right h2 gp)
          (ensures unshared left right h2 y /\ reshaped left right h0 h2 gp y /\
                   (let rt = rot_for w0 w1 (nodes view left right h0 gp) in
                    nodes view left right h2 y == replace rt gp (recolorn (sub rt gp) true)))
  = bal_mid view left right h0 h1 root cur par gp ggp y w0 w1;
    nodes_sub view left right h1 y gp;
    graft_at view left right h1 h2 y gp;
    reshaped_trans left right h0 h1 h2 gp y y

/// What `ReplaceChildOrRoot(p, c, c')` does: `root` becomes `c'` when `p` is null, and
/// otherwise `p`'s link to `c` becomes `c'`.
let replaced (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (root0 root1 p c c': B.box r) : prop =
  (B.is_null p ==> root1 == c' /\ h1 == h0) /\
  (B.is_null p == false ==> root1 == root0 /\ relinked view left right h0 h1 p c c')

/// `relink_ltree` for trees of views.
let relink_nodes (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1: heap r) (root c c': B.box r)
  : Lemma (requires unshared left right h0 root /\ L.memP c (nboxes (nodes view left right h0 root)) /\
                    B.is_null c == false /\
                    Cons? (fst (focus (nodes view left right h0 root) c)) /\
                    unshared left right h0 c' /\
                    distinct (nboxes (replace (nodes view left right h0 root) c (nodes view left right h0 c'))) /\
                    relinked view left right h0 h1 (Cons?.hd (fst (focus (nodes view left right h0 root) c))).fbox c c')
          (ensures unshared left right h1 root /\
                   nodes view left right h1 root ==
                     replace (nodes view left right h0 root) c (nodes view left right h0 c'))
  = let lt = ltree left right h0 root in
    nboxes_boxes lt;
    focus_bmap view lt c;
    replace_bmap view lt c (ltree left right h0 c');
    nboxes_boxes (replace lt c (ltree left right h0 c'));
    relink_ltree view left right h0 h1 root c c'

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
/// The end of `InsertionBalance`.
let bal_end (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h0 h1 h2 h3 h4: heap r) (root0 root1 cur par0 par1 gp ggp y: B.box r) (w0 w1: bool)
  : Lemma (requires balance_pre view left right h0 root0 cur par0 gp ggp /\
                    bal_sides view left right h0 root0 cur w0 w1 /\
                    rotated view left right h0 h1 gp y w0 w1 /\
                    reshaped left right h0 h1 gp y /\ unshared left right h1 y /\
                    recolored view left right h1 h2 gp true /\
                    reshaped left right h1 h2 gp gp /\ unshared left right h2 gp /\
                    recolored view left right h2 h3 y false /\
                    reshaped left right h2 h3 y y /\ unshared left right h3 y /\
                    replaced view left right h3 h4 root0 root1 ggp gp y /\
                    par1 == (if w0 = w1 then par0 else ggp))
          (ensures balanced view left right h0 h4 root0 root1 cur par0 par1 ggp)
  = let (f0, f1, rest, s) = bal_focus view left right h0 root0 cur par0 gp ggp in
    let n0 = nodes view left right h0 root0 in
    let tg = fill f1 (fill f0 s) in
    bal_red view left right h0 h1 h2 root0 cur par0 gp ggp y w0 w1;
    reshaped_trans left right h0 h2 h3 gp y y;
    let bs = balance_sub w0 w1 tg in
    assert (nodes view left right h3 y == bs);
    balance_sub_shape f0 f1 s;
    bal_boxes f0 f1 s;
    assert (same_side n0 cur == (w0 = w1));
    if B.is_null ggp then begin
      (match rest with [] -> () | f :: _ -> assert (L.memP f.fbox (nboxes n0)));
      assert (rest == []);
      assert (balance n0 cur == bs)
    end else begin
      assert (L.memP gp (nboxes bs));
      graft_nodes view left right h0 h3 root0 gp y;
      let n3 = nodes view left right h3 root0 in
      top_ltree left right h3 gp;
      nboxes_boxes (ltree left right h3 gp);
      replace_twice n0 gp (nodes view left right h3 gp) bs;
      (match rest with
       | [] -> ()
       | f :: _ -> assert (f.fbox == ggp));
      relink_nodes view left right h3 h4 root0 gp y
    end
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* The insertion                                                                         *)

/// `k0` with `k` inserted where it belongs.
let inserted (#t: Type0) (c: O.comparer t) (k0: Seq.seq t) (k: t) : Seq.seq t =
  seq_ins k0 (S.lower_bound c k0 k) k

/// The tree at `root` is a set of `k1`'s keys, red-black but for its root.
let okp (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k1: Seq.seq t) (h: heap r) (root: B.box r) : prop =
  unshared left right h root /\ ok c k1 (nodes view left right h root)

/// The loop is done: `parent` is the node the new one hangs from.
let at_end (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h: heap r) (root par gp ggp: B.box r) (o: int)
  : Lemma (requires inv view left right c k0 k h root B.null par gp ggp o)
          (ensures B.is_null par == false /\ mem h par /\ unshared left right h par /\
                   L.memP par (nboxes (nodes view left right h root)))
  = let n = nodes view left right h root in
    let (fs, s) = descent_elim c k n B.null par gp ggp o in
    (match s with
     | T.Branch _ _ _ -> ok_focus c k0 fs s; assert (B.is_null #r B.null)
     | T.Leaf -> ());
    let f0 :: rest = fs in
    mem_plug par fs s;
    at_box view left right h root par

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
/// `parent.Left`/`parent.Right = node`, the new red node holding `k`.
let linked_leaf (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k0: Seq.seq t) (k: t) (h h2: heap r) (root x par gp ggp: B.box r) (o: int)
  : Lemma (requires inv view left right c k0 k h root B.null par gp ggp o /\
                    ~ (mem h x) /\ B.is_null x == false /\
                    mem h2 x /\ B.is_null (left (get h2 x)) /\ B.is_null (right (get h2 x)) /\
                    view x (get h2 x) == (k, true) /\
                    mem h par /\ mem h2 par /\ view par (get h2 par) == view par (get h par) /\
                    (o > 0 ==> right (get h2 par) == x /\ left (get h2 par) == left (get h par)) /\
                    (o <= 0 ==> left (get h2 par) == x /\ right (get h2 par) == right (get h par)) /\
                    framed h h2 [par])
          (ensures S.key_index c k0 k < 0 /\ unshared left right h2 root /\
                   (~ (par_red view left right h2 par) ==> okp view left right c (inserted c k0 k) h2 root) /\
                   (par_red view left right h2 par ==>
                      balance_pre view left right h2 root x par gp ggp /\
                      ok c (inserted c k0 k) (balance (nodes view left right h2 root) x)))
  = at_end view left right c k0 k h root par gp ggp o;
    let n = nodes view left right h root in
    let vp = get h par in
    let vp2 = get h2 par in
    let vx = get h2 x in
    let sib = if o > 0 then left vp else right vp in
    unshared_step left right h par;
    unshared_elim left right h sib;
    let ls = ltree left right h sib in
    let lx : T.tree (B.box r & r) = T.Branch T.Leaf (x, vx) T.Leaf in
    let tl = if o > 0 then T.Branch ls (par, vp2) lx else T.Branch lx (par, vp2) ls in
    (* `par`'s old child on the search's side is null: the descent ended there. *)
    let (fs, s) = descent_elim c k n B.null par gp ggp o in
    (match s with
     | T.Branch _ _ _ -> ok_focus c k0 fs s; assert (B.is_null #r B.null)
     | T.Leaf -> ());
    let f0 :: rest = fs in
    focus_at rest (fill f0 s);
    at_box view left right h root par;
    assert (f0.went_right == (o > 0));
    realizes_framed left right h h2 sib ls [par];
    FStar.Classical.move_requires (realizes_mem left right h sib ls) x;
    assert (~ (L.memP x (boxes ls)) /\ ~ (L.memP par (boxes ls)) /\ ~ (x == par));
    assert (realizes left right h2 x lx);
    assert_norm (boxes lx == [x]);
    assert (distinct (boxes ls));
    assert_norm (distinct [x]);
    let dj (y: B.box r) : Lemma (L.memP y [x] <==> y == x) = () in
    FStar.Classical.forall_intro dj;
    assert (disjoint (boxes ls) [x] /\ disjoint [x] (boxes ls));
    if o > 0 then begin
      assert (left vp2 == sib /\ right vp2 == x);
      assert (realizes left right h2 par tl);
      assert (boxes tl == par :: L.append (boxes ls) [x]);
      assert (distinct (boxes tl))
    end else begin
      assert (left vp2 == x /\ right vp2 == sib);
      assert (realizes left right h2 par tl);
      assert (boxes tl == par :: L.append [x] (boxes ls));
      assert (distinct (boxes tl))
    end;
    assert (distinct (boxes tl));
    unshared_intro left right h2 par tl;
    let lp = ltree left right h par in
    unshared_elim left right h par;
    let fr_ (y: B.box r) : Lemma (L.memP y [par] ==> L.memP y (boxes lp)) = () in
    FStar.Classical.forall_intro fr_;
    framed_mono h h2 [par] (boxes lp);
    assert (reshaped left right h h2 par par);
    graft left right h h2 root par;
    unshared_elim left right h root;
    nboxes_boxes (ltree left right h root);
    let lr = ltree left right h root in
    replace_bmap view lr par tl;
    assert (nodes view left right h2 root == replace n par (bmap view tl));
    assert (bmap view tl == (if o > 0 then T.Branch (nodes view left right h sib) (par, view par vp) (leaf x k)
                             else T.Branch (leaf x k) (par, view par vp) (nodes view left right h sib)));
    assert (nodes view left right h2 root == set_child n par (o > 0) (leaf x k));
    FStar.Classical.move_requires (realizes_mem left right h root lr) x;
    insert_leaf c k0 k n par gp ggp o x;
    let n1 = nodes view left right h2 root in
    if nred (sub n1 par) then par_red_at view left right h2 root par
    else par_red_at view left right h2 root par
#pop-options

/// After `InsertionBalance(node, …)`.
let after_insert_balance (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k1: Seq.seq t) (h2 h3: heap r) (root root3 x par par3 ggp: B.box r)
  : Lemma (requires ok c k1 (balance (nodes view left right h2 root) x) /\
                    balanced view left right h2 h3 root root3 x par par3 ggp)
          (ensures okp view left right c k1 h3 root3)
  = ()

/// `root.ColorBlack()` after the insertion.
let finish_ok (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (c: O.comparer t) (k1: Seq.seq t) (h0 h1: heap r) (root: B.box r)
  : Lemma (requires okp view left right c k1 h0 root /\ recolored view left right h0 h1 root false)
          (ensures ST.keys (tree_of view left right h1 root) == k1 /\
                   S.strictly_sorted c k1 /\
                   ST.red_black (tree_of view left right h1 root) /\
                   T.size (tree_of view left right h1 root) == Seq.length k1)
  = finish view left right c k1 h0 h1 root

(* ------------------------------------------------------------------------------------ *)
(* For the C# side                                                                       *)
(* These patterns come last, so the proofs above do not see them.                        *)

/// The `int` the program reads from `comparer.Compare` is the sign `cmp` stands for.
let cmp_i32 (#t: Type0) (c: O.comparer t) (x y: t)
  : Lemma (ensures FStar.Int32.v (S.compare_i32 c x y) == cmp c x y)
          [SMTPat (S.compare_i32 c x y)]
  = ()

/// `nodes` unfolds one level, so a helper's writes can be followed in boxes as in views.
let bmap_branch (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2) (l: T.tree (B.box r & e1)) (b: B.box r)
    (v: e1) (rr: T.tree (B.box r & e1))
  : Lemma (ensures bmap g (T.Branch l (b, v) rr) == T.Branch (bmap g l) (b, g b v) (bmap g rr))
          [SMTPat (bmap g (T.Branch l (b, v) rr))]
  = ()

let bmap_leaf (#r #e1 #e2: Type0) (g: B.box r -> e1 -> e2)
  : Lemma (ensures bmap g (T.Leaf #(B.box r & e1)) == T.Leaf)
          [SMTPat (bmap g (T.Leaf #(B.box r & e1)))]
  = ()

let nodes_ltree (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (x: B.box r)
  : Lemma (ensures nodes view left right h x == bmap view (ltree left right h x))
          [SMTPat (nodes view left right h x)]
  = ()

/// The insertion adds one key.
let inserted_length (#t: Type0) (c: O.comparer t) (k0: Seq.seq t) (k: t)
  : Lemma (ensures Seq.length (inserted c k0 k) == Seq.length k0 + 1)
          [SMTPat (Seq.length (inserted c k0 k))]
  = seq_ins_index k0 (S.lower_bound c k0 k) k 0

/// Inserting into the empty set gives the keys of a lone node.
let inserted_empty (#t: Type0) (c: O.comparer t) (k0: Seq.seq t) (k: t)
  : Lemma (requires Seq.length k0 == 0)
          (ensures inserted c k0 k == Seq.append Seq.empty (Seq.cons k Seq.empty))
          [SMTPat (inserted c k0 k)]
  = seq_ins_index k0 (S.lower_bound c k0 k) k 0;
    Seq.lemma_eq_intro (inserted c k0 k) (Seq.append Seq.empty (Seq.cons k Seq.empty))

/// `InsertionBalance`'s parent and grandparent are nodes of the tree, so not null.
let balance_pre_nonnull (#r #t: Type0) (view: B.box r -> r -> (t & bool)) (left right: r -> B.box r)
    (h: heap r) (root cur par gp ggp: B.box r)
  : Lemma (requires balance_pre view left right h root cur par gp ggp)
          (ensures B.is_null par == false /\ B.is_null gp == false)
          [SMTPat (balance_pre view left right h root cur par gp ggp)]
  = let n = nodes view left right h root in
    let fs = fst (focus n cur) in
    mem_plug par fs (sub n cur);
    mem_plug gp fs (sub n cur)

/// `++count` below `int.MaxValue`: the `Int.size` guard with `pow2 31` evaluated, which a
/// method as large as `AddIfNotPresent` does not otherwise get to within its rlimit.
let size_succ (n: int)
  : Lemma (requires -2147483648 <= n /\ n < 2147483647) (ensures FStar.Int.size (n + 1) 32)
          [SMTPat (FStar.Int.size (n + 1) 32)]
  = assert_norm (pow2 31 == 2147483648)
