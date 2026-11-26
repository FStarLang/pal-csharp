module SortedSetInductive.StateCases

module O = SortedSetInductive.Ownership
module Q = SortedSetInductive.State
module C = SortedSetInductive.StateCorrespondence
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree

#set-options "--z3rlimit 10"

let raw (key: int) (l r: N.class_Node__opt int) : N.class_Node__raw int =
  { N.fld_Item = key; N.fld_Color = O.color false; N.fld_Left = l; N.fld_Right = r }

// The SAME saved retired record observes the UPDATED live subtree. It is
// neither a singleton substitute nor a frozen interpretation of old links.
let changed_live (x y z: N.class_Node__opt int)
  : Lemma (requires not (B.is_null x) /\ not (B.is_null y) /\ not (B.is_null z) /\
      x =!= y /\ x =!= z /\ y =!= z)
    (ensures (
      let old = FStar.Ghost.hide (T.Branch T.Leaf (y, (2, false)) T.Leaf,
        O.Cell x (raw 1 y B.null) O.End) in
      let now = FStar.Ghost.hide (T.Branch T.Leaf (y, (20, false))
        (T.Branch T.Leaf (z, (3, false)) T.Leaf), O.Cell x (raw 1 y B.null) O.End) in
      Q.find (Q.observe old) x == Q.find (Q.observe now) x /\
      Q.tree_at (Q.observe old) x ==
        T.Branch (T.Branch T.Leaf (2, false) T.Leaf) (1, false) T.Leaf /\
      Q.tree_at (Q.observe now) x ==
        T.Branch (T.Branch T.Leaf (20, false) (T.Branch T.Leaf (3, false) T.Leaf))
          (1, false) T.Leaf)) =
  reveal_opaque (`%Q.tree_at) (Q.tree_at #int)

let self_cycle (x: N.class_Node__opt int)
  : Lemma (requires not (B.is_null x))
    (ensures (
      let s = FStar.Ghost.hide (T.Leaf, O.Cell x (raw 7 x B.null) O.End) in
      Q.fuel (Q.observe s) == 2 /\ Q.mem (Q.observe s) x /\ not (Q.wf (Q.observe s) x) /\
      Q.tree_at (Q.observe s) x ==
        T.Branch (T.Branch T.Leaf (7, false) T.Leaf) (7, false) T.Leaf)) =
  reveal_opaque (`%Q.tree_at) (Q.tree_at #int);
  reveal_opaque (`%Q.wf) (Q.wf #int)

let missing_link (x y: N.class_Node__opt int)
  : Lemma (requires not (B.is_null x) /\ not (B.is_null y) /\ x =!= y)
    (ensures (
      let s = FStar.Ghost.hide (T.Leaf, O.Cell x (raw 7 y B.null) O.End) in
      Q.mem (Q.observe s) x /\ not (Q.mem (Q.observe s) y) /\ not (Q.wf (Q.observe s) x) /\
      Q.tree_at (Q.observe s) x == T.Branch T.Leaf (7, false) T.Leaf)) =
  reveal_opaque (`%Q.tree_at) (Q.tree_at #int);
  reveal_opaque (`%Q.wf) (Q.wf #int)

// Re-abstracting a retired tree into a cell and two forests cannot change
// the observation value, hence cannot change ANY exposed model projection.
let reabstract_retired (#a: Type0) (active l r: O.tree a)
    (e: N.class_Node__opt a & (a & bool)) (rest: O.retired a)
  : Lemma (
      Q.observe (FStar.Ghost.hide (active, O.Forest (T.Branch l e r) rest)) ==
      Q.observe (FStar.Ghost.hide
        (active, O.Cell (fst e) (Q.record l e r) (O.Forest l (O.Forest r rest))))) =
  let old = Q.observe (FStar.Ghost.hide (active, O.Forest (T.Branch l e r) rest)) in
  let now = Q.observe (FStar.Ghost.hide
    (active, O.Cell (fst e) (Q.record l e r) (O.Forest l (O.Forest r rest)))) in
  let at (x: N.class_Node__opt a) : Lemma (Q.find old x == Q.find now x) =
    match Q.find_tree active x with
    | Some _ -> ()
    | None ->
      if Pulse.Lib.CSharp.RefEq.ref_eq (fst e) x then ()
      else match Q.find_tree l x with | Some _ -> () | None -> () in
  FStar.Classical.forall_intro at;
  Q.observation_equal old now
