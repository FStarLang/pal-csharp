module InductiveRemoveRotation

module C = InductiveCursor
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove
module P = Pulse.Lib.CSharp.RegionPath
module T = Pulse.Lib.CSharp.Tree
module S = Pulse.Lib.CSharp.SearchTree
module M = InductiveMutation
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let target (#a: Type0) (n: C.tree a) (right: bool) =
  if right then P.top (T.right (T.right n)) else P.top (T.left (T.left n))
let observed_target (#a: Type0) (n: C.tree a) (right: bool) =
  let root = P.sub n (P.top n) in
  let child = if right then T.right root else T.left root in
  let at_child = P.sub n (P.top child) in
  P.top (if right then T.right at_child else T.left at_child)
let prepared (#a: Type0) (n: C.tree a) (right: bool) =
  M.recolor n (target n right) false
let single_rotation (right: bool) = if right then S.RotLeft else S.RotRight
let can_rotate (#a: Type0) (rot: S.tree_rotation) (n: C.tree a) =
  T.Branch? n /\
  (match rot with
   | S.RotLeft -> T.Branch? (T.right n) /\ T.Branch? (T.right (T.right n))
   | S.RotRight -> T.Branch? (T.left n) /\ T.Branch? (T.left (T.left n))
   | S.RotLeftRight -> T.Branch? (T.left n) /\ T.Branch? (T.right (T.left n))
   | S.RotRightLeft -> T.Branch? (T.right n) /\ T.Branch? (T.left (T.right n)))

let single (#a: Type0) (n: C.tree a) (right: bool)
  : Lemma
    (requires C.good n /\ can_rotate (single_rotation right) n)
    (ensures target n right == observed_target n right /\ C.member n (target n right) /\
      P.top (prepared n right) == P.top n /\
      (if right then S.rot_left (prepared n right) else S.rot_right (prepared n right))
        == R.rotn (single_rotation right) n)
  = assert (T.Branch? n);
    C.lookup_root n;
    C.lookup_children n (P.top n);
    let T.Branch l pv r = n in
    if right then (
      assert (T.Branch? r /\ T.Branch? (T.right r));
      let T.Branch rl qv rr = r in
      let f0 = {P.went_right=true; P.fbox=fst qv; P.fval=snd qv; P.fsib=rl} in
      let f1 = {P.went_right=true; P.fbox=fst pv; P.fval=snd pv; P.fsib=l} in
      assert_norm (P.plug [f0;f1] rr == P.fill f1 (P.fill f0 rr));
      assert (P.plug [f0;f1] rr == n);
      D.focus_at [f0;f1] rr;
      assert (P.top rr =!= B.null);
      assert_norm (P.plug [f0;f1] (D.recolorn rr false) ==
        P.fill f1 (P.fill f0 (D.recolorn rr false)));
      assert (prepared n right == T.Branch l pv (T.Branch rl qv (D.recolorn rr false))))
    else (
      assert (T.Branch? l /\ T.Branch? (T.left l));
      let T.Branch ll qv lr = l in
      let f0 = {P.went_right=false; P.fbox=fst qv; P.fval=snd qv; P.fsib=lr} in
      let f1 = {P.went_right=false; P.fbox=fst pv; P.fval=snd pv; P.fsib=r} in
      assert_norm (P.plug [f0;f1] ll == P.fill f1 (P.fill f0 ll));
      assert (P.plug [f0;f1] ll == n);
      D.focus_at [f0;f1] ll;
      assert (P.top ll =!= B.null);
      assert_norm (P.plug [f0;f1] (D.recolorn ll false) ==
        P.fill f1 (P.fill f0 (D.recolorn ll false)));
      assert (prepared n right == T.Branch (T.Branch (D.recolorn ll false) qv lr) pv r))
