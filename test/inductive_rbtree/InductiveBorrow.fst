module InductiveBorrow

module C = InductiveCursor
module N = Class_RbNode
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove
module P = Pulse.Lib.CSharp.RegionPath
module S = Pulse.Lib.CSharp.SearchTree
module M = InductiveMutation
module X = InductiveRemoveRotation
module T = Pulse.Lib.CSharp.Tree

#set-options "--z3rlimit 10"

let colored (#a: Type0) (n: C.tree a) (rot: S.tree_rotation) =
  D.recolorn (R.rotn rot n) true
let blackened (#a: Type0) (n: C.tree a) (rot: S.tree_rotation) =
  M.recolor (colored n rot) (P.top n) false
let borrowed (#a: Type0) (n: C.tree a) (cur: N.class_RbNode__opt a) (rot: S.tree_rotation) =
  M.recolor (blackened n rot) cur true
let ready (#a: Type0) (n: C.tree a) (cur: N.class_RbNode__opt a) (rot: S.tree_rotation) =
  X.can_rotate rot n /\
  C.member (R.rotn rot n) (P.top n) /\
  D.nred (P.sub (R.rotn rot n) (P.top n)) /\
  C.member (colored n rot) (P.top n) /\
  C.member (blackened n rot) cur

let choose (left red: bool) =
  if red then (if left then S.RotRightLeft else S.RotRight)
  else (if left then S.RotLeft else S.RotLeftRight)

let left_color (#a: Type0) (n: C.tree a) (sib: N.class_RbNode__opt a)
  : Lemma (requires C.good n /\ C.member n sib)
    (ensures S.is_red (C.lookup n (P.top (T.left (P.sub n sib)))) ==
      D.nred (T.left (P.sub n sib)))
  = C.lookup_children n sib
