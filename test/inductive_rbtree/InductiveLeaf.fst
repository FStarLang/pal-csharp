module InductiveLeaf
#lang-pulse

open Pulse.Lib.Pervasives
module C = InductiveCursor
module O = InductiveOwnership
module N = Class_RbNode
module D = Pulse.Lib.CSharp.TopDown
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module B = Pulse.Lib.Box
module L = FStar.List.Tot

#set-options "--z3rlimit 10"

let attach (#a: Type0) (n u: C.tree a) (right: bool) : C.tree a =
  match n with
  | T.Leaf -> T.Leaf
  | T.Branch l e r -> if right then T.Branch l e u else T.Branch u e r

ghost fn make_leaf (#a: Type0) (x: N.class_RbNode__opt a) (key: a) (red: bool)
  requires O.held x key red B.null B.null
  ensures C.owns (D.recolorn (D.leaf x key) red) ** pure (x =!= B.null)
{
  B.pts_to_not_null x;
  fold (C.owns (T.Leaf <: C.tree a));
  fold (C.owns (T.Leaf <: C.tree a));
  fold (C.owns (T.Branch T.Leaf (x, (key, red)) T.Leaf));
  rewrite (C.owns (T.Branch T.Leaf (x, (key, red)) T.Leaf))
    as (C.owns (D.recolorn (D.leaf x key) red));
}

ghost fn fresh (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) (key: a)
  preserves C.owns n ** C.owns (D.leaf x key)
  ensures pure (~ (L.memP x (P.nboxes n)))
{
  rewrite (C.owns (D.leaf x key)) as (C.owns (T.Branch T.Leaf (x, (key, true)) T.Leaf));
  unfold (C.owns (T.Branch T.Leaf (x, (key, true)) T.Leaf));
  C.apart_cell n x {N.fld_key=key; N.fld_red=true; N.fld_left=B.null; N.fld_right=B.null};
  fold (C.owns (T.Branch T.Leaf (x, (key, true)) T.Leaf));
  rewrite (C.owns (T.Branch T.Leaf (x, (key, true)) T.Leaf)) as (C.owns (D.leaf x key));
}

ghost fn attach_leaves (#a: Type0) (n u: C.tree a) (right: bool)
  requires C.owns (T.left n) ** C.owns (T.right n) ** C.owns u **
    pure (T.Branch? n /\ (if right then T.right n == T.Leaf else T.left n == T.Leaf))
  ensures C.owns (T.left (attach n u right)) ** C.owns (T.right (attach n u right))
{
  if (right) {
    rewrite (C.owns (T.right n)) as emp;
    rewrite (C.owns (T.left n)) as (C.owns (T.left (attach n u right)));
    rewrite (C.owns u) as (C.owns (T.right (attach n u right)));
  } else {
    rewrite (C.owns (T.left n)) as emp;
    rewrite (C.owns (T.right n)) as (C.owns (T.right (attach n u right)));
    rewrite (C.owns u) as (C.owns (T.left (attach n u right)));
  }
}
