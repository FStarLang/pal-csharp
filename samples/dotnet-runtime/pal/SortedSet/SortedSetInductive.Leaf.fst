module SortedSetInductive.Leaf
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module E = SortedSetInductive.Edit
module N = Class_Node
module D = Pulse.Lib.CSharp.TopDown
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module S = Pulse.Lib.CSharp.SearchTree
module K = SortedSetInductive.Relink
module Local = SortedSetInductive.Local

#set-options "--z3rlimit 10"

let attach (#a: Type0) (n u: O.tree a) (right: bool) : O.tree a =
  match n with
  | T.Leaf -> T.Leaf
  | T.Branch l e r -> if right then T.Branch l e u else T.Branch u e r

let black_leaf (#a: Type0) (x: N.class_Node__opt a) (key: a) =
  D.recolorn (D.leaf x key) false

let linked (#a: Type0) (n: O.tree a) (parent x: N.class_Node__opt a) (key: a) (right: bool) =
  D.set_child n parent right (D.leaf x key)

ghost fn release_empty (#a: Type0) (n: O.tree a)
  requires O.owns n 1.0R ** pure (O.good n /\ P.top n == B.null)
  ensures pure (n == T.Leaf)
{
  assert (pure (n == T.Leaf));
  rewrite (O.owns n 1.0R) as emp;
}

ghost fn make_leaf (#a: Type0) (x: N.class_Node__opt a) (key: a) (red: bool)
  requires O.held x key red B.null B.null 1.0R
  ensures O.owns (D.recolorn (D.leaf x key) red) 1.0R ** pure (x =!= B.null)
{
  B.pts_to_not_null x;
  fold (O.owns (T.Leaf <: O.tree a) 1.0R);
  fold (O.owns (T.Leaf <: O.tree a) 1.0R);
  fold (O.owns (T.Branch T.Leaf (x, (key, red)) T.Leaf) 1.0R);
  rewrite (O.owns (T.Branch T.Leaf (x, (key, red)) T.Leaf) 1.0R)
    as (O.owns (D.recolorn (D.leaf x key) red) 1.0R);
}

ghost fn fresh (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (key: a)
  preserves O.owns n 1.0R ** O.owns (D.leaf x key) 1.0R
  ensures pure (~ (L.memP x (P.nboxes n)))
{
  rewrite (O.owns (D.leaf x key) 1.0R) as (O.owns (T.Branch T.Leaf (x, (key, true)) T.Leaf) 1.0R);
  unfold (O.owns (T.Branch T.Leaf (x, (key, true)) T.Leaf) 1.0R);
  E.apart_cell n x {N.fld_Item=key; N.fld_Color=S.Red; N.fld_Left=B.null; N.fld_Right=B.null};
  fold (O.owns (T.Branch T.Leaf (x, (key, true)) T.Leaf) 1.0R);
  rewrite (O.owns (T.Branch T.Leaf (x, (key, true)) T.Leaf) 1.0R) as (O.owns (D.leaf x key) 1.0R);
}

ghost fn attach_leaves (#a: Type0) (n u: O.tree a) (right: bool)
  requires O.owns (T.left n) 1.0R ** O.owns (T.right n) 1.0R ** O.owns u 1.0R **
    pure (T.Branch? n /\ (if right then T.right n == T.Leaf else T.left n == T.Leaf))
  ensures O.owns (T.left (attach n u right)) 1.0R ** O.owns (T.right (attach n u right)) 1.0R
{
  if (right) {
    rewrite (O.owns (T.right n) 1.0R) as emp;
    rewrite (O.owns (T.left n) 1.0R) as (O.owns (T.left (attach n u right)) 1.0R);
    rewrite (O.owns u 1.0R) as (O.owns (T.right (attach n u right)) 1.0R);
  } else {
    rewrite (O.owns (T.left n) 1.0R) as emp;
    rewrite (O.owns (T.right n) 1.0R) as (O.owns (T.right (attach n u right)) 1.0R);
    rewrite (O.owns u 1.0R) as (O.owns (T.left (attach n u right)) 1.0R);
  }
}

unfold let link_slot (#a: Type0) (parent: N.class_Node__opt a) (n: O.tree a)
    (x: N.class_Node__opt a) (right: bool) =
  exists* (v: N.class_Node__raw a).
    O.raw parent v 1.0R ** O.owns (T.left n) 1.0R ** O.owns (T.right n) 1.0R **
    pure (n == T.Branch (T.left n) (parent, O.entry v) (T.right n) /\
      v.N.fld_Left == (if right then P.top (T.left n) else x) /\
      v.N.fld_Right == (if right then x else P.top (T.right n)))

ghost fn open_link (#a: Type0) (n: O.tree a) (parent: N.class_Node__opt a)
  requires O.owns n 1.0R ** pure (O.good n /\ O.member n parent)
  ensures Local.opened parent (P.sub n parent) ** K.pending n parent
{
  SortedSetInductive.Cursor.lookup_children n parent;
  K.cut n parent;
  Local.open_node parent (P.sub n parent);
}

ghost fn close_link (#a: Type0) (n: O.tree a) (parent x: N.class_Node__opt a)
    (key: a) (right: bool)
  requires link_slot parent (P.sub n parent) x right **
    O.owns (D.leaf x key) 1.0R ** K.pending n parent **
    pure (if right then T.right (P.sub n parent) == T.Leaf else T.left (P.sub n parent) == T.Leaf)
  ensures O.owns (linked n parent x key right) 1.0R
{
  unfold (link_slot parent (P.sub n parent) x right);
  with v. _;
  attach_leaves (P.sub n parent) (D.leaf x key) right;
  fold (Local.opened parent (attach (P.sub n parent) (D.leaf x key) right));
  Local.close_node parent (attach (P.sub n parent) (D.leaf x key) right);
  K.join_same n parent (attach (P.sub n parent) (D.leaf x key) right);
  rewrite (O.owns (P.replace n parent (attach (P.sub n parent) (D.leaf x key) right)) 1.0R)
    as (O.owns (linked n parent x key right) 1.0R);
}
