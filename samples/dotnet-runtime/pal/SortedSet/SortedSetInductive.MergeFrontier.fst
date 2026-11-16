module SortedSetInductive.MergeFrontier
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module L = SortedSetInductive.Local
module F = SortedSetInductive.Frontier
module K = SortedSetInductive.Relink
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove

#set-options "--z3rlimit 10"

let read_facts (#a: Type0) (n: O.tree a)
  : Lemma (R.is2 n ==
      (T.Branch? n && not (D.nred n) &&
        not (O.nullable_red (F.optional (T.left n))) &&
        not (O.nullable_red (F.optional (T.right n)))))
  = F.optional_red (T.left n); F.optional_red (T.right n)

unfold let after (#a: Type0) (x: N.class_Node__opt a) (n: O.tree a) =
  exists* (v vl vr: N.class_Node__raw a).
    O.raw x v 1.0R ** O.raw v.N.fld_Left vl 1.0R ** O.raw v.N.fld_Right vr 1.0R **
    F.below (T.left n) ** F.below (T.right n) **
    pure (x == P.top (D.merge2n n) /\ F.optional (D.merge2n n) == Some v /\
      F.optional (T.left (D.merge2n n)) == Some vl /\ F.optional (T.right (D.merge2n n)) == Some vr)

ghost fn open_merge (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires O.owns n 1.0R **
    pure (O.member n x /\ T.Branch? (T.left (P.sub n x)) /\ T.Branch? (T.right (P.sub n x)))
  ensures F.split_cells x (P.sub n x) ** K.pending n x
{
  P.focus_plug n x;
  K.cut n x;
  L.open_node x (P.sub n x);
  unfold (L.opened x (P.sub n x));
  with v. _;
  L.open_node v.N.fld_Left (T.left (P.sub n x));
  L.open_node v.N.fld_Right (T.right (P.sub n x));
  unfold (L.opened v.N.fld_Left (T.left (P.sub n x)));
  with vl. _;
  unfold (L.opened v.N.fld_Right (T.right (P.sub n x)));
  with vr. _;
  fold (F.split_cells x (P.sub n x));
}

ghost fn close_merge (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires after x (P.sub n x) ** K.pending n x **
    pure (O.member n x /\ T.Branch? (T.left (P.sub n x)) /\ T.Branch? (T.right (P.sub n x)))
  ensures O.owns (P.replace n x (D.merge2n (P.sub n x))) 1.0R
{
  let u = D.merge2n (P.sub n x);
  unfold (after x (P.sub n x));
  with v vl vr. _;
  F.snapshot_facts u v;
  F.snapshot_facts (T.left u) vl;
  F.snapshot_facts (T.right u) vr;
  unfold (F.below (T.left (P.sub n x)));
  unfold (F.below (T.right (P.sub n x)));
  L.color_leaves (T.left (P.sub n x)) true;
  L.color_leaves (T.right (P.sub n x)) true;
  rewrite each (D.recolorn (T.left (P.sub n x)) true) as (T.left u);
  rewrite each (D.recolorn (T.right (P.sub n x)) true) as (T.right u);
  L.close_node v.N.fld_Left (T.left u);
  L.close_node v.N.fld_Right (T.right u);
  L.close_node x u;
  K.join_same n x u;
  rewrite (O.owns (P.replace n x u) 1.0R) as
    (O.owns (P.replace n x (D.merge2n (P.sub n x))) 1.0R);
}
