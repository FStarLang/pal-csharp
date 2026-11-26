module InductiveLocal
#lang-pulse

open Pulse.Lib.Pervasives
module C = InductiveCursor
module O = InductiveOwnership
module N = Class_RbNode
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module B = Pulse.Lib.Box
module S = Pulse.Lib.CSharp.SearchTree
module D = Pulse.Lib.CSharp.TopDown

#set-options "--z3rlimit 10"

ghost fn color_leaves (#a: Type0) (n: C.tree a) (red: bool)
  requires C.owns (T.left n) ** C.owns (T.right n) ** pure (T.Branch? n)
  ensures C.owns (T.left (D.recolorn n red)) ** C.owns (T.right (D.recolorn n red))
{
  rewrite (C.owns (T.left n)) as (C.owns (T.left (D.recolorn n red)));
  rewrite (C.owns (T.right n)) as (C.owns (T.right (D.recolorn n red)));
}

ghost fn split_leaves (#a: Type0) (n: C.tree a)
  requires C.owns (D.recolorn (T.left n) false) ** C.owns (D.recolorn (T.right n) false) **
    pure (T.Branch? n)
  ensures C.owns (T.left (D.split4n n)) ** C.owns (T.right (D.split4n n))
{
  rewrite (C.owns (D.recolorn (T.left n) false)) as (C.owns (T.left (D.split4n n)));
  rewrite (C.owns (D.recolorn (T.right n) false)) as (C.owns (T.right (D.split4n n)));
}

ghost fn black_leaves (#a: Type0) (n: C.tree a)
  requires C.owns (T.left n) ** C.owns (T.right n) ** pure (T.Branch? n)
  ensures C.owns (T.left (D.recolorn n false)) ** C.owns (T.right (D.recolorn n false))
{
  color_leaves n false;
}

ghost fn red_leaves (#a: Type0) (n: C.tree a)
  requires C.owns (T.left n) ** C.owns (T.right n) ** pure (T.Branch? n)
  ensures C.owns (T.left (D.recolorn n true)) ** C.owns (T.right (D.recolorn n true))
{
  color_leaves n true;
}

ghost fn merge_leaves (#a: Type0) (n: C.tree a)
  requires C.owns (D.recolorn (T.left n) true) ** C.owns (D.recolorn (T.right n) true) **
    pure (T.Branch? n)
  ensures C.owns (T.left (D.merge2n n)) ** C.owns (T.right (D.merge2n n))
{
  rewrite (C.owns (D.recolorn (T.left n) true)) as (C.owns (T.left (D.merge2n n)));
  rewrite (C.owns (D.recolorn (T.right n) true)) as (C.owns (T.right (D.merge2n n)));
}

unfold let opened (#a: Type0) (root: N.class_RbNode__opt a) (n: C.tree a) =
  exists* (k: a) (red: bool) (l r: N.class_RbNode__opt a).
    O.held root k red l r ** C.owns (T.left n) ** C.owns (T.right n) **
    pure (n == T.Branch (T.left n) (root, (k, red)) (T.right n) /\
      l == P.top (T.left n) /\ r == P.top (T.right n))

ghost fn open_node (#a: Type0) (root: N.class_RbNode__opt a) (n: C.tree a)
  requires C.owns n ** pure (T.Branch? n /\ root == P.top n)
  ensures opened root n ** pure (root =!= B.null)
{
  rewrite (C.owns n) as (C.owns (T.Branch (T.left n) (T.Branch?._1 n) (T.right n)));
  unfold (C.owns (T.Branch (T.left n) (T.Branch?._1 n) (T.right n)));
  rewrite each (fst (T.Branch?._1 n)) as root;
  B.pts_to_not_null root;
}

ghost fn close_node (#a: Type0) (root: N.class_RbNode__opt a) (n: C.tree a)
  requires opened root n
  ensures C.owns n ** pure (root == P.top n)
{
  unfold (opened root n);
  with k red l r. _;
  rewrite (O.held root k red l r) as (O.held root k red (P.top (T.left n)) (P.top (T.right n)));
  fold (C.owns (T.Branch (T.left n) (root, (k, red)) (T.right n)));
  rewrite (C.owns (T.Branch (T.left n) (root, (k, red)) (T.right n))) as (C.owns n);
}

ghost fn left_leaves (#a: Type0) (n: C.tree a)
  requires C.owns (T.left n) ** C.owns (T.left (T.right n)) ** C.owns (T.right (T.right n)) **
    pure (T.Branch? n /\ T.Branch? (T.right n))
  ensures C.owns (T.left (T.left (S.rot_left n))) **
    C.owns (T.right (T.left (S.rot_left n))) ** C.owns (T.right (S.rot_left n))
{
  rewrite (C.owns (T.left n)) as (C.owns (T.left (T.left (S.rot_left n))));
  rewrite (C.owns (T.left (T.right n))) as (C.owns (T.right (T.left (S.rot_left n))));
  rewrite (C.owns (T.right (T.right n))) as (C.owns (T.right (S.rot_left n)));
}

ghost fn right_leaves (#a: Type0) (n: C.tree a)
  requires C.owns (T.left (T.left n)) ** C.owns (T.right (T.left n)) ** C.owns (T.right n) **
    pure (T.Branch? n /\ T.Branch? (T.left n))
  ensures C.owns (T.left (S.rot_right n)) **
    C.owns (T.left (T.right (S.rot_right n))) ** C.owns (T.right (T.right (S.rot_right n)))
{
  rewrite (C.owns (T.left (T.left n))) as (C.owns (T.left (S.rot_right n)));
  rewrite (C.owns (T.right (T.left n))) as (C.owns (T.left (T.right (S.rot_right n))));
  rewrite (C.owns (T.right n)) as (C.owns (T.right (T.right (S.rot_right n))));
}

ghost fn left_right_leaves (#a: Type0) (n: C.tree a)
  requires C.owns (T.left (T.left n)) ** C.owns (T.left (T.right (T.left n))) **
    C.owns (T.right (T.right (T.left n))) ** C.owns (T.right n) **
    pure (T.Branch? n /\ T.Branch? (T.left n) /\ T.Branch? (T.right (T.left n)))
  ensures C.owns (T.left (T.left (S.rot_left_right n))) **
    C.owns (T.right (T.left (S.rot_left_right n))) **
    C.owns (T.left (T.right (S.rot_left_right n))) **
    C.owns (T.right (T.right (S.rot_left_right n)))
{
  rewrite (C.owns (T.left (T.left n))) as (C.owns (T.left (T.left (S.rot_left_right n))));
  rewrite (C.owns (T.left (T.right (T.left n)))) as (C.owns (T.right (T.left (S.rot_left_right n))));
  rewrite (C.owns (T.right (T.right (T.left n)))) as (C.owns (T.left (T.right (S.rot_left_right n))));
  rewrite (C.owns (T.right n)) as (C.owns (T.right (T.right (S.rot_left_right n))));
}

ghost fn right_left_leaves (#a: Type0) (n: C.tree a)
  requires C.owns (T.left n) ** C.owns (T.left (T.left (T.right n))) **
    C.owns (T.right (T.left (T.right n))) ** C.owns (T.right (T.right n)) **
    pure (T.Branch? n /\ T.Branch? (T.right n) /\ T.Branch? (T.left (T.right n)))
  ensures C.owns (T.left (T.left (S.rot_right_left n))) **
    C.owns (T.right (T.left (S.rot_right_left n))) **
    C.owns (T.left (T.right (S.rot_right_left n))) **
    C.owns (T.right (T.right (S.rot_right_left n)))
{
  rewrite (C.owns (T.left n)) as (C.owns (T.left (T.left (S.rot_right_left n))));
  rewrite (C.owns (T.left (T.left (T.right n)))) as (C.owns (T.right (T.left (S.rot_right_left n))));
  rewrite (C.owns (T.right (T.left (T.right n)))) as (C.owns (T.left (T.right (S.rot_right_left n))));
  rewrite (C.owns (T.right (T.right n))) as (C.owns (T.right (T.right (S.rot_right_left n))));
}
