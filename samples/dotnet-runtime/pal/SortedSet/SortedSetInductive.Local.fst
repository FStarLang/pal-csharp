module SortedSetInductive.Local
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module B = Pulse.Lib.Box
module S = Pulse.Lib.CSharp.SearchTree
module D = Pulse.Lib.CSharp.TopDown

#set-options "--z3rlimit 10"

unfold let opened (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a) =
  exists* (v: N.class_Node__raw a).
    O.raw root v 1.0R ** O.owns (T.left n) 1.0R ** O.owns (T.right n) 1.0R **
    pure (n == T.Branch (T.left n) (root, O.entry v) (T.right n) /\
      v.N.fld_Left == P.top (T.left n) /\ v.N.fld_Right == P.top (T.right n))

ghost fn open_node (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a)
  requires O.owns n 1.0R ** pure (T.Branch? n /\ root == P.top n)
  ensures opened root n ** pure (root =!= B.null)
{
  rewrite (O.owns n 1.0R) as (O.owns (T.Branch (T.left n) (T.Branch?._1 n) (T.right n)) 1.0R);
  unfold (O.owns (T.Branch (T.left n) (T.Branch?._1 n) (T.right n)) 1.0R);
  rewrite each (fst (T.Branch?._1 n)) as root;
  B.pts_to_not_null root;
}

ghost fn close_node (#a: Type0) (root: N.class_Node__opt a) (n: O.tree a)
  requires opened root n
  ensures O.owns n 1.0R ** pure (root == P.top n)
{
  unfold (opened root n);
  with v. _;
  rewrite (O.raw root v 1.0R) as (O.held root (O.item v) (O.red v) (P.top (T.left n)) (P.top (T.right n)) 1.0R);
  fold (O.owns (T.Branch (T.left n) (root, O.entry v) (T.right n)) 1.0R);
  rewrite (O.owns (T.Branch (T.left n) (root, O.entry v) (T.right n)) 1.0R) as (O.owns n 1.0R);
}

ghost fn color_leaves (#a: Type0) (n: O.tree a) (red: bool)
  requires O.owns (T.left n) 1.0R ** O.owns (T.right n) 1.0R ** pure (T.Branch? n)
  ensures O.owns (T.left (D.recolorn n red)) 1.0R ** O.owns (T.right (D.recolorn n red)) 1.0R
{
  rewrite (O.owns (T.left n) 1.0R) as (O.owns (T.left (D.recolorn n red)) 1.0R);
  rewrite (O.owns (T.right n) 1.0R) as (O.owns (T.right (D.recolorn n red)) 1.0R);
}

ghost fn split_leaves (#a: Type0) (n: O.tree a)
  requires O.owns (D.recolorn (T.left n) false) 1.0R ** O.owns (D.recolorn (T.right n) false) 1.0R **
    pure (T.Branch? n)
  ensures O.owns (T.left (D.split4n n)) 1.0R ** O.owns (T.right (D.split4n n)) 1.0R
{
  rewrite (O.owns (D.recolorn (T.left n) false) 1.0R) as (O.owns (T.left (D.split4n n)) 1.0R);
  rewrite (O.owns (D.recolorn (T.right n) false) 1.0R) as (O.owns (T.right (D.split4n n)) 1.0R);
}

ghost fn merge_leaves (#a: Type0) (n: O.tree a)
  requires O.owns (D.recolorn (T.left n) true) 1.0R ** O.owns (D.recolorn (T.right n) true) 1.0R **
    pure (T.Branch? n)
  ensures O.owns (T.left (D.merge2n n)) 1.0R ** O.owns (T.right (D.merge2n n)) 1.0R
{
  rewrite (O.owns (D.recolorn (T.left n) true) 1.0R) as (O.owns (T.left (D.merge2n n)) 1.0R);
  rewrite (O.owns (D.recolorn (T.right n) true) 1.0R) as (O.owns (T.right (D.merge2n n)) 1.0R);
}

ghost fn left_leaves (#a: Type0) (n: O.tree a)
  requires O.owns (T.left n) 1.0R ** O.owns (T.left (T.right n)) 1.0R ** O.owns (T.right (T.right n)) 1.0R **
    pure (T.Branch? n /\ T.Branch? (T.right n))
  ensures O.owns (T.left (T.left (S.rot_left n))) 1.0R **
    O.owns (T.right (T.left (S.rot_left n))) 1.0R ** O.owns (T.right (S.rot_left n)) 1.0R
{
  rewrite (O.owns (T.left n) 1.0R) as (O.owns (T.left (T.left (S.rot_left n))) 1.0R);
  rewrite (O.owns (T.left (T.right n)) 1.0R) as (O.owns (T.right (T.left (S.rot_left n))) 1.0R);
  rewrite (O.owns (T.right (T.right n)) 1.0R) as (O.owns (T.right (S.rot_left n)) 1.0R);
}

ghost fn right_leaves (#a: Type0) (n: O.tree a)
  requires O.owns (T.left (T.left n)) 1.0R ** O.owns (T.right (T.left n)) 1.0R ** O.owns (T.right n) 1.0R **
    pure (T.Branch? n /\ T.Branch? (T.left n))
  ensures O.owns (T.left (S.rot_right n)) 1.0R **
    O.owns (T.left (T.right (S.rot_right n))) 1.0R ** O.owns (T.right (T.right (S.rot_right n))) 1.0R
{
  rewrite (O.owns (T.left (T.left n)) 1.0R) as (O.owns (T.left (S.rot_right n)) 1.0R);
  rewrite (O.owns (T.right (T.left n)) 1.0R) as (O.owns (T.left (T.right (S.rot_right n))) 1.0R);
  rewrite (O.owns (T.right n) 1.0R) as (O.owns (T.right (T.right (S.rot_right n))) 1.0R);
}

ghost fn left_right_leaves (#a: Type0) (n: O.tree a)
  requires O.owns (T.left (T.left n)) 1.0R ** O.owns (T.left (T.right (T.left n))) 1.0R **
    O.owns (T.right (T.right (T.left n))) 1.0R ** O.owns (T.right n) 1.0R **
    pure (T.Branch? n /\ T.Branch? (T.left n) /\ T.Branch? (T.right (T.left n)))
  ensures O.owns (T.left (T.left (S.rot_left_right n))) 1.0R **
    O.owns (T.right (T.left (S.rot_left_right n))) 1.0R **
    O.owns (T.left (T.right (S.rot_left_right n))) 1.0R **
    O.owns (T.right (T.right (S.rot_left_right n))) 1.0R
{
  rewrite (O.owns (T.left (T.left n)) 1.0R) as (O.owns (T.left (T.left (S.rot_left_right n))) 1.0R);
  rewrite (O.owns (T.left (T.right (T.left n))) 1.0R) as (O.owns (T.right (T.left (S.rot_left_right n))) 1.0R);
  rewrite (O.owns (T.right (T.right (T.left n))) 1.0R) as (O.owns (T.left (T.right (S.rot_left_right n))) 1.0R);
  rewrite (O.owns (T.right n) 1.0R) as (O.owns (T.right (T.right (S.rot_left_right n))) 1.0R);
}

ghost fn right_left_leaves (#a: Type0) (n: O.tree a)
  requires O.owns (T.left n) 1.0R ** O.owns (T.left (T.left (T.right n))) 1.0R **
    O.owns (T.right (T.left (T.right n))) 1.0R ** O.owns (T.right (T.right n)) 1.0R **
    pure (T.Branch? n /\ T.Branch? (T.right n) /\ T.Branch? (T.left (T.right n)))
  ensures O.owns (T.left (T.left (S.rot_right_left n))) 1.0R **
    O.owns (T.right (T.left (S.rot_right_left n))) 1.0R **
    O.owns (T.left (T.right (S.rot_right_left n))) 1.0R **
    O.owns (T.right (T.right (S.rot_right_left n))) 1.0R
{
  rewrite (O.owns (T.left n) 1.0R) as (O.owns (T.left (T.left (S.rot_right_left n))) 1.0R);
  rewrite (O.owns (T.left (T.left (T.right n))) 1.0R) as (O.owns (T.right (T.left (S.rot_right_left n))) 1.0R);
  rewrite (O.owns (T.right (T.left (T.right n))) 1.0R) as (O.owns (T.left (T.right (S.rot_right_left n))) 1.0R);
  rewrite (O.owns (T.right (T.right n)) 1.0R) as (O.owns (T.right (T.right (S.rot_right_left n))) 1.0R);
}
