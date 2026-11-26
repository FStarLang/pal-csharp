module SortedSetInductive.Selector
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module L = SortedSetInductive.Local
module E = SortedSetInductive.Edit
module Q = SortedSetInductive.Rotation
module F = SortedSetInductive.Frontier
module X = SortedSetInductive.RemoveDispatch
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let rest (#a: Type0) (n: O.tree a) (dir: bool) =
  O.owns (Q.child n (not dir)) 1.0R ** O.owns (T.right (Q.child n dir)) 1.0R **
  F.below (T.left (Q.child n dir))

// A preserved observation frontier for parent.GetRotation(current, sibling).
// Rotate consumes this very frontier, restoring it before opening its write
// frontier. Thus no proof needs to split the original nested runtime call.
unfold let window (#a: Type0) (root sibling: N.class_Node__opt a) (n: O.tree a) (dir: bool) =
  exists* (v w: N.class_Node__raw a) (left: O.nullable_snapshot a).
    O.raw root v 1.0R ** O.raw sibling w 1.0R **
    O.nullable_raw w.N.fld_Left left 1.0R ** rest n dir **
    pure (root == P.top n /\ sibling == P.top (Q.child n dir) /\
      root =!= B.null /\ sibling =!= B.null /\
      Q.shape n v /\ Q.linked n v /\
      Q.shape (Q.child n dir) w /\ Q.linked (Q.child n dir) w /\
      left == F.optional (T.left (Q.child n dir)) /\
      O.nullable_red left == D.nred (T.left (Q.child n dir)))

ghost fn open_selector (#a: Type0) (root sibling: N.class_Node__opt a) (n: O.tree a) (dir: bool)
  requires O.owns n 1.0R **
    pure (root == P.top n /\ sibling == P.top (Q.child n dir) /\ T.Branch? n /\ T.Branch? (Q.child n dir))
  ensures window root sibling n dir
{
  X.open_two root n dir;
  unfold (X.two root n dir);
  with v w. _;
  rewrite (O.raw (X.link v dir) w 1.0R) as (O.raw sibling w 1.0R);
  F.open_optional (T.left (Q.child n dir));
  F.optional_red (T.left (Q.child n dir));
  rewrite (O.nullable_raw (P.top (T.left (Q.child n dir))) (F.optional (T.left (Q.child n dir))) 1.0R)
    as (O.nullable_raw w.N.fld_Left (F.optional (T.left (Q.child n dir))) 1.0R);
  fold (rest n dir);
}

ghost fn close_selector (#a: Type0) (root sibling: N.class_Node__opt a) (n: O.tree a) (dir: bool)
  requires window root sibling n dir
  ensures O.owns n 1.0R
{
  unfold (window root sibling n dir);
  with v w left. _;
  unfold (rest n dir);
  rewrite (O.nullable_raw w.N.fld_Left left 1.0R)
    as (O.nullable_raw (P.top (T.left (Q.child n dir))) (F.optional (T.left (Q.child n dir))) 1.0R);
  F.close_optional (T.left (Q.child n dir));
  rewrite (O.raw sibling w 1.0R) as (O.raw (P.top (Q.child n dir)) w 1.0R);
  L.close_node (P.top (Q.child n dir)) (Q.child n dir);
  if dir {
    E.change (Q.child n dir) (T.right n);
    E.change (Q.child n (not dir)) (T.left n);
    L.close_node root n;
  } else {
    E.change (Q.child n dir) (T.left n);
    E.change (Q.child n (not dir)) (T.right n);
    L.close_node root n;
  }
}
