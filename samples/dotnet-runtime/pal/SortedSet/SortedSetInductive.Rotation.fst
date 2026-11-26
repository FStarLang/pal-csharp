module SortedSetInductive.Rotation
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module L = SortedSetInductive.Local
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module S = Pulse.Lib.CSharp.SearchTree
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let child (#a: Type0) (n: O.tree a) (right: bool) =
  if right then T.right n else T.left n
let single (#a: Type0) (n: O.tree a) (right: bool) =
  if right then S.rot_left n else S.rot_right n
let shape (#a: Type0) (n: O.tree a) (v: N.class_Node__raw a) =
  T.Branch? n /\ n == T.Branch (T.left n) (P.top n, O.entry v) (T.right n)
let linked (#a: Type0) (n: O.tree a) (v: N.class_Node__raw a) =
  v.N.fld_Left == P.top (T.left n) /\ v.N.fld_Right == P.top (T.right n)

let single_fringe (#a: Type0) (n: O.tree a) (right: bool) =
  if right then
    O.owns (T.left n) 1.0R ** O.owns (T.left (T.right n)) 1.0R ** O.owns (T.right (T.right n)) 1.0R
  else
    O.owns (T.left (T.left n)) 1.0R ** O.owns (T.right (T.left n)) 1.0R ** O.owns (T.right n) 1.0R

unfold let single_before (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (right: bool) =
  exists* (v w: N.class_Node__raw a).
    O.raw root v 1.0R ** O.raw (if right then v.N.fld_Right else v.N.fld_Left) w 1.0R **
    single_fringe n right **
    pure (root == P.top n /\ shape n v /\ shape (child n right) w /\
      linked n v /\ linked (child n right) w)

unfold let single_after (#a: Type0) (root pivot: N.class_Node__opt a) (n: O.tree a) (right: bool) =
  exists* (v w: N.class_Node__raw a) (index: bool).
    O.raw root v 1.0R ** O.raw pivot w 1.0R **
    single_fringe n index **
    pure (index == right /\ root == P.top n /\ pivot == P.top (child n right) /\
      shape n v /\ shape (child n right) w /\
        (if right then
          v.N.fld_Left == P.top (T.left n) /\ v.N.fld_Right == P.top (T.left (T.right n)) /\
          w.N.fld_Left == P.top n /\ w.N.fld_Right == P.top (T.right (T.right n))
        else
          v.N.fld_Left == P.top (T.right (T.left n)) /\ v.N.fld_Right == P.top (T.right n) /\
          w.N.fld_Left == P.top (T.left (T.left n)) /\ w.N.fld_Right == P.top n))

ghost fn open_single (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (right: bool)
  requires O.owns n 1.0R ** pure (root == P.top n /\ T.Branch? n /\ T.Branch? (child n right))
  ensures single_before root n right **
    pure (root =!= B.null /\ P.top (child n right) =!= B.null)
{
  L.open_node root n;
  unfold (L.opened root n);
  with v. _;
  if right {
    L.open_node (P.top (T.right n)) (T.right n);
    unfold (L.opened (P.top (T.right n)) (T.right n));
    with w. _;
    rewrite (O.raw (P.top (T.right n)) w 1.0R) as (O.raw v.N.fld_Right w 1.0R);
    fold (single_fringe n right);
  } else {
    L.open_node (P.top (T.left n)) (T.left n);
    unfold (L.opened (P.top (T.left n)) (T.left n));
    with w. _;
    rewrite (O.raw (P.top (T.left n)) w 1.0R) as (O.raw v.N.fld_Left w 1.0R);
    fold (single_fringe n right);
  }
}

ghost fn close_single (#a: Type0) (root pivot: N.class_Node__opt a) (n: O.tree a) (right: bool)
  requires single_after root pivot n right
  ensures O.owns (single n right) 1.0R **
    pure (P.top (single n right) == P.top (child n right) /\ pivot == P.top (single n right))
{
  unfold (single_after root pivot n right);
  with v w index. _;
  rewrite (single_fringe n index) as (single_fringe n right);
  unfold (single_fringe n right);
  if right {
    L.left_leaves n;
    L.close_node root (T.left (S.rot_left n));
    L.close_node pivot (S.rot_left n);
  } else {
    L.right_leaves n;
    L.close_node root (T.right (S.rot_right n));
    L.close_node pivot (S.rot_right n);
  }
}

unfold let single_ignored (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (right: bool) =
  exists* (pivot: N.class_Node__opt a). single_after root pivot n right

ghost fn close_ignored (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (right: bool)
  requires single_ignored root n right
  ensures O.owns (single n right) 1.0R
{
  unfold (single_ignored root n right);
  with pivot. _;
  close_single root pivot n right;
}

let double_child (#a: Type0) (n: O.tree a) (right: bool) = child n (not right)
let grand (#a: Type0) (n: O.tree a) (right: bool) = child (double_child n right) right
let double (#a: Type0) (n: O.tree a) (right: bool) =
  if right then S.rot_left_right n else S.rot_right_left n

let double_fringe (#a: Type0) (n: O.tree a) (right: bool) =
  if right then
    O.owns (T.left (T.left n)) 1.0R ** O.owns (T.left (T.right (T.left n))) 1.0R **
    O.owns (T.right (T.right (T.left n))) 1.0R ** O.owns (T.right n) 1.0R
  else
    O.owns (T.left n) 1.0R ** O.owns (T.left (T.left (T.right n))) 1.0R **
    O.owns (T.right (T.left (T.right n))) 1.0R ** O.owns (T.right (T.right n)) 1.0R

unfold let double_before (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (right: bool) =
  exists* (v w z: N.class_Node__raw a).
    O.raw root v 1.0R **
    O.raw (if right then v.N.fld_Left else v.N.fld_Right) w 1.0R **
    O.raw (if right then w.N.fld_Right else w.N.fld_Left) z 1.0R **
    double_fringe n right **
    pure (root == P.top n /\ shape n v /\ shape (double_child n right) w /\ shape (grand n right) z /\
      linked n v /\ linked (double_child n right) w /\ linked (grand n right) z)

unfold let double_after (#a: Type0) (root pivot: N.class_Node__opt a) (n: O.tree a) (right: bool) =
  exists* (v z wt wf: N.class_Node__raw a) (xt xf: N.class_Node__opt a) (index: bool).
    O.raw root v 1.0R ** O.raw pivot z 1.0R **
    (match right with | true -> O.raw xt wt 1.0R | false -> O.raw xf wf 1.0R) **
    double_fringe n index **
    pure (index == right /\ root == P.top n /\ pivot == P.top (grand n right) /\
      shape n v /\ shape (grand n right) z /\
      (if right then
        xt == z.N.fld_Left /\ shape (double_child n right) wt /\
        v.N.fld_Left == P.top (T.right (grand n right)) /\ v.N.fld_Right == P.top (T.right n) /\
        wt.N.fld_Left == P.top (T.left (double_child n right)) /\ wt.N.fld_Right == P.top (T.left (grand n right)) /\
        z.N.fld_Left == P.top (double_child n right) /\ z.N.fld_Right == P.top n
      else
        xf == z.N.fld_Right /\ shape (double_child n right) wf /\
        v.N.fld_Left == P.top (T.left n) /\ v.N.fld_Right == P.top (T.left (grand n right)) /\
        wf.N.fld_Left == P.top (T.right (grand n right)) /\ wf.N.fld_Right == P.top (T.right (double_child n right)) /\
        z.N.fld_Left == P.top n /\ z.N.fld_Right == P.top (double_child n right)))

ghost fn open_double (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (right: bool)
  requires O.owns n 1.0R **
    pure (root == P.top n /\ T.Branch? n /\ T.Branch? (double_child n right) /\ T.Branch? (grand n right))
  ensures double_before root n right **
    pure (root =!= B.null /\ P.top (double_child n right) =!= B.null /\ P.top (grand n right) =!= B.null)
{
  L.open_node root n;
  unfold (L.opened root n);
  with v. _;
  if right {
    L.open_node (P.top (T.left n)) (T.left n);
    unfold (L.opened (P.top (T.left n)) (T.left n));
    with w. _;
    L.open_node (P.top (T.right (T.left n))) (T.right (T.left n));
    unfold (L.opened (P.top (T.right (T.left n))) (T.right (T.left n)));
    with z. _;
    rewrite (O.raw (P.top (T.left n)) w 1.0R) as (O.raw v.N.fld_Left w 1.0R);
    rewrite (O.raw (P.top (T.right (T.left n))) z 1.0R) as (O.raw w.N.fld_Right z 1.0R);
    fold (double_fringe n right);
  } else {
    L.open_node (P.top (T.right n)) (T.right n);
    unfold (L.opened (P.top (T.right n)) (T.right n));
    with w. _;
    L.open_node (P.top (T.left (T.right n))) (T.left (T.right n));
    unfold (L.opened (P.top (T.left (T.right n))) (T.left (T.right n)));
    with z. _;
    rewrite (O.raw (P.top (T.right n)) w 1.0R) as (O.raw v.N.fld_Right w 1.0R);
    rewrite (O.raw (P.top (T.left (T.right n))) z 1.0R) as (O.raw w.N.fld_Left z 1.0R);
    fold (double_fringe n right);
  }
}

ghost fn close_double (#a: Type0) (root pivot: N.class_Node__opt a) (n: O.tree a) (right: bool)
  requires double_after root pivot n right
  ensures O.owns (double n right) 1.0R **
    pure (P.top (double n right) == P.top (grand n right) /\ pivot == P.top (double n right))
{
  unfold (double_after root pivot n right);
  with v z wt wf xt xf index. _;
  rewrite (double_fringe n index) as (double_fringe n right);
  unfold (double_fringe n right);
  if right {
    L.left_right_leaves n;
    L.close_node xt (T.left (S.rot_left_right n));
    L.close_node root (T.right (S.rot_left_right n));
    L.close_node pivot (S.rot_left_right n);
  } else {
    L.right_left_leaves n;
    L.close_node root (T.left (S.rot_right_left n));
    L.close_node xf (T.right (S.rot_right_left n));
    L.close_node pivot (S.rot_right_left n);
  }
}
