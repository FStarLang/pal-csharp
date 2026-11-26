module SortedSetInductive.RemoveDispatch
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module L = SortedSetInductive.Local
module E = SortedSetInductive.Edit
module Q = SortedSetInductive.Rotation
module X = SortedSetInductive.RemoveRotation
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module S = Pulse.Lib.CSharp.SearchTree
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let right (rot: S.tree_rotation) =
  match rot with S.RotLeft | S.RotRightLeft -> true | _ -> false
let grand_right (rot: S.tree_rotation) =
  match rot with S.RotLeft | S.RotLeftRight -> true | _ -> false
let is_single (rot: S.tree_rotation) =
  match rot with S.RotLeft | S.RotRight -> true | _ -> false
let child (#a: Type0) (n: O.tree a) (rot: S.tree_rotation) = Q.child n (right rot)
let grand (#a: Type0) (n: O.tree a) (rot: S.tree_rotation) = Q.child (child n rot) (grand_right rot)
let first_other (#a: Type0) (n: O.tree a) (rot: S.tree_rotation) = Q.child n (not (right rot))
let second_other (#a: Type0) (n: O.tree a) (rot: S.tree_rotation) =
  Q.child (child n rot) (not (grand_right rot))
let link (#a: Type0) (v: N.class_Node__raw a) (dir: bool) =
  if dir then v.N.fld_Right else v.N.fld_Left
let root_after (#a: Type0) (n: O.tree a) (rot: S.tree_rotation) =
  Q.child (R.rotn rot n) (not (right rot))
let other_after (#a: Type0) (n: O.tree a) (rot: S.tree_rotation) =
  Q.child (R.rotn rot n) (right rot)

// Exactly three records, with the four untouched recursively owned fringes.
// The same frontier works before and after the dispatcher's direct returns.
let fringe (#a: Type0) (n: O.tree a) (rot: S.tree_rotation) =
  O.owns (first_other n rot) 1.0R ** O.owns (second_other n rot) 1.0R **
  O.owns (T.left (grand n rot)) 1.0R ** O.owns (T.right (grand n rot)) 1.0R

unfold let before (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (rot: S.tree_rotation) =
  exists* (v w z: N.class_Node__raw a).
    O.raw root v 1.0R ** O.raw (link v (right rot)) w 1.0R **
    O.raw (link w (grand_right rot)) z 1.0R ** fringe n rot **
    pure (root == P.top n /\ root =!= B.null /\
      P.top (child n rot) =!= B.null /\ P.top (grand n rot) =!= B.null /\
      Q.shape n v /\ Q.linked n v /\
      Q.shape (child n rot) w /\ Q.linked (child n rot) w /\
      Q.shape (grand n rot) z /\ Q.linked (grand n rot) z)

unfold let after_color (#a: Type0) (root pivot: N.class_Node__opt a) (n: O.tree a) (rot: S.tree_rotation) (red: bool) =
  exists* (v w z: N.class_Node__raw a) (other: N.class_Node__opt a) (index: S.tree_rotation).
    O.raw root v 1.0R ** O.raw pivot w 1.0R ** O.raw other z 1.0R ** fringe n index **
    pure (index == rot /\ X.can_rotate rot n /\ root == P.top n /\ pivot == P.top (R.rotn rot n) /\
      other == P.top (other_after n rot) /\
      Q.shape (root_after n rot) v /\ Q.linked (root_after n rot) v /\
      Q.shape (D.recolorn (R.rotn rot n) red) w /\ Q.linked (R.rotn rot n) w /\
      Q.shape (other_after n rot) z /\ Q.linked (other_after n rot) z)

unfold let after (#a: Type0) (root pivot: N.class_Node__opt a) (n: O.tree a) (rot: S.tree_rotation) =
  after_color root pivot n rot (D.nred (R.rotn rot n))

ghost fn specialize (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (from into: S.tree_rotation)
  requires before root n from ** pure (from == into)
  ensures before root n into
{
  rewrite (before root n from) as (before root n into);
}

ghost fn impossible (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (rot: S.tree_rotation)
  requires before root n rot ** pure False
  ensures after root B.null n rot ** pure False
{
  unreachable ();
}

unfold let two (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (dir: bool) =
  exists* (v w: N.class_Node__raw a).
    O.raw root v 1.0R ** O.raw (link v dir) w 1.0R **
    O.owns (Q.child n (not dir)) 1.0R **
    O.owns (T.left (Q.child n dir)) 1.0R ** O.owns (T.right (Q.child n dir)) 1.0R **
    pure (root == P.top n /\ root =!= B.null /\ P.top (Q.child n dir) =!= B.null /\
      Q.shape n v /\ Q.linked n v /\
      Q.shape (Q.child n dir) w /\ Q.linked (Q.child n dir) w)

ghost fn open_two (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (dir: bool)
  requires O.owns n 1.0R ** pure (root == P.top n /\ T.Branch? n /\ T.Branch? (Q.child n dir))
  ensures two root n dir
{
  Q.open_single root n dir;
  unfold (Q.single_before root n dir);
  with v w. _;
  unfold (Q.single_fringe n dir);
  if dir {
    rewrite (O.owns (T.left n) 1.0R) as (O.owns (Q.child n (not dir)) 1.0R);
    rewrite (O.owns (T.left (T.right n)) 1.0R) as (O.owns (T.left (Q.child n dir)) 1.0R);
    rewrite (O.owns (T.right (T.right n)) 1.0R) as (O.owns (T.right (Q.child n dir)) 1.0R);
  } else {
    rewrite (O.owns (T.right n) 1.0R) as (O.owns (Q.child n (not dir)) 1.0R);
    rewrite (O.owns (T.left (T.left n)) 1.0R) as (O.owns (T.left (Q.child n dir)) 1.0R);
    rewrite (O.owns (T.right (T.left n)) 1.0R) as (O.owns (T.right (Q.child n dir)) 1.0R);
  }
}

ghost fn open_dispatch (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) (rot: S.tree_rotation)
  requires O.owns n 1.0R ** pure (root == P.top n /\ X.can_rotate rot n)
  ensures before root n rot
{
  open_two root n (right rot);
  unfold (two root n (right rot));
  with v w. _;
  if (grand_right rot) {
    L.open_node (P.top (T.right (child n rot))) (T.right (child n rot));
    unfold (L.opened (P.top (T.right (child n rot))) (T.right (child n rot)));
    with z. _;
    rewrite (O.owns (T.left (child n rot)) 1.0R) as (O.owns (second_other n rot) 1.0R);
    rewrite (O.owns (T.left (T.right (child n rot))) 1.0R) as (O.owns (T.left (grand n rot)) 1.0R);
    rewrite (O.owns (T.right (T.right (child n rot))) 1.0R) as (O.owns (T.right (grand n rot)) 1.0R);
    rewrite (O.raw (P.top (T.right (child n rot))) z 1.0R) as (O.raw (link w (grand_right rot)) z 1.0R);
    fold (fringe n rot);
  } else {
    L.open_node (P.top (T.left (child n rot))) (T.left (child n rot));
    unfold (L.opened (P.top (T.left (child n rot))) (T.left (child n rot)));
    with z. _;
    rewrite (O.owns (T.right (child n rot)) 1.0R) as (O.owns (second_other n rot) 1.0R);
    rewrite (O.owns (T.left (T.left (child n rot))) 1.0R) as (O.owns (T.left (grand n rot)) 1.0R);
    rewrite (O.owns (T.right (T.left (child n rot))) 1.0R) as (O.owns (T.right (grand n rot)) 1.0R);
    rewrite (O.raw (P.top (T.left (child n rot))) z 1.0R) as (O.raw (link w (grand_right rot)) z 1.0R);
    fold (fringe n rot);
  }
}

ghost fn close_colored (#a: Type0) (root pivot: N.class_Node__opt a) (n: O.tree a) (rot: S.tree_rotation) (red: bool)
  requires after_color root pivot n rot red
  ensures O.owns (D.recolorn (R.rotn rot n) red) 1.0R ** pure (pivot == P.top (R.rotn rot n))
{
  unfold (after_color root pivot n rot red);
  with v w z other index. _;
  rewrite (fringe n index) as (fringe n rot);
  unfold (fringe n rot);
  match rot {
    S.RotLeft -> {
      E.change (T.left (grand n rot)) (T.left (other_after n rot));
      E.change (T.right (grand n rot)) (T.right (other_after n rot));
      E.change (first_other n rot) (T.left (root_after n rot));
      E.change (second_other n rot) (T.right (root_after n rot));
      L.close_node other (other_after n rot);
      L.close_node root (root_after n rot);
      L.color_leaves (R.rotn rot n) red;
      L.close_node pivot (D.recolorn (R.rotn rot n) red);
    }
    S.RotRight -> {
      E.change (T.left (grand n rot)) (T.left (other_after n rot));
      E.change (T.right (grand n rot)) (T.right (other_after n rot));
      E.change (first_other n rot) (T.right (root_after n rot));
      E.change (second_other n rot) (T.left (root_after n rot));
      L.close_node other (other_after n rot);
      L.close_node root (root_after n rot);
      L.color_leaves (R.rotn rot n) red;
      L.close_node pivot (D.recolorn (R.rotn rot n) red);
    }
    S.RotLeftRight -> {
      E.change (first_other n rot) (T.right (root_after n rot));
      E.change (second_other n rot) (T.left (other_after n rot));
      E.change (T.left (grand n rot)) (T.right (other_after n rot));
      E.change (T.right (grand n rot)) (T.left (root_after n rot));
      L.close_node other (other_after n rot);
      L.close_node root (root_after n rot);
      L.color_leaves (R.rotn rot n) red;
      L.close_node pivot (D.recolorn (R.rotn rot n) red);
    }
    S.RotRightLeft -> {
      E.change (first_other n rot) (T.left (root_after n rot));
      E.change (second_other n rot) (T.right (other_after n rot));
      E.change (T.left (grand n rot)) (T.right (root_after n rot));
      E.change (T.right (grand n rot)) (T.left (other_after n rot));
      L.close_node other (other_after n rot);
      L.close_node root (root_after n rot);
      L.color_leaves (R.rotn rot n) red;
      L.close_node pivot (D.recolorn (R.rotn rot n) red);
    }

  }
}

ghost fn close_dispatch (#a: Type0) (root pivot: N.class_Node__opt a) (n: O.tree a) (rot: S.tree_rotation)
  requires after root pivot n rot
  ensures O.owns (R.rotn rot n) 1.0R ** pure (pivot == P.top (R.rotn rot n))
{
  unfold (after root pivot n rot);
  close_colored root pivot n rot (D.nred (R.rotn rot n));
  E.change (D.recolorn (R.rotn rot n) (D.nred (R.rotn rot n))) (R.rotn rot n);
}
