module SortedSetInductive.Edit
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Forall.Util
open Pulse.Lib.Trade.Util
module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Cursor
module N = Class_Node
module P = Pulse.Lib.CSharp.RegionPath
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module L = FStar.List.Tot
module RT = Pulse.Lib.CSharp.RegionTree
module D = Pulse.Lib.CSharp.TopDown

#set-options "--z3rlimit 10"

unfold let retained (#a: Type0) (s: O.state a) =
  O.retained (O.retired_state s) 1.0R

ghost fn change (#a: Type0) (n u: O.tree a)
  requires O.owns n 1.0R ** pure (n == u)
  ensures O.owns u 1.0R
{
  rewrite (O.owns n 1.0R) as (O.owns u 1.0R);
}

// A recursive ancestor context can restore any replacement subtree whose
// root pointer is unchanged. Root-changing stores use the context directly.
let restore (#a: Type0) (fs: list (C.frame a))
    (hole: N.class_Node__opt a) (p: perm) =
  forall* (t: O.tree a).
    (pure (P.top t == hole) ** O.owns t p) @==> O.owns (P.plug fs t) p

ghost fn context_trade (#a: Type0) (fs: list (C.frame a))
    (hole: N.class_Node__opt a) (p: perm)
  requires C.context fs hole p
  ensures restore fs hole p
{
  intro (forall* (t: O.tree a).
    (pure (P.top t == hole) ** O.owns t p) @==> O.owns (P.plug fs t) p)
    #(C.context fs hole p) fn _ t {
      rewrite (C.context fs hole p) as (C.context fs (P.top t) p);
      C.join fs t p;
    };
  fold (restore fs hole p);
}

ghost fn focus (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires O.owns t p
  ensures O.owns (P.sub t x) p **
    restore (fst (P.focus t x)) (P.top (P.sub t x)) p
{
  P.focus_plug t x;
  rewrite (O.owns t p) as (O.owns (P.plug (fst (P.focus t x)) (P.sub t x)) p);
  C.split (fst (P.focus t x)) (P.sub t x) p;
  context_trade (fst (P.focus t x)) (P.top (P.sub t x)) p;
}

ghost fn restore_focus (#a: Type0) (fs: list (C.frame a)) (t: O.tree a) (p: perm)
  requires O.owns t p ** restore fs (P.top t) p
  ensures O.owns (P.plug fs t) p
{
  unfold (restore fs (P.top t) p);
  Pulse.Lib.Forall.Util.elim
    #_ #(fun s -> (pure (P.top s == P.top t) ** O.owns s p) @==> O.owns (P.plug fs s) p) t;
  Pulse.Lib.Trade.Util.elim _ _;
}

// Keep the retired forest as a genuine spatial resource while the active
// tree changes. These rules never convert, discard, or duplicate ownership.
ghost fn begin_owner (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
  requires O.owner root s 1.0R
  ensures O.owns (O.active s) 1.0R ** O.retained (O.retired_state s) 1.0R **
    pure (root == P.top (O.active s))
{
  unfold (O.owner root s 1.0R);
}

ghost fn end_owner (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (t: erased (O.tree a))
  requires O.owns (reveal t) 1.0R ** O.retained (O.retired_state s) 1.0R **
    pure (root == P.top (reveal t))
  ensures O.owner root (O.replace s t) 1.0R
{
  fold (O.owner root (O.replace s t) 1.0R);
}

ghost fn cells_distinct (#a: Type0) (x y: N.class_Node__opt a)
    (vx vy: N.class_Node__raw a)
  preserves O.raw x vx 1.0R ** O.raw y vy 1.0R
  ensures pure (x =!= y)
{
  if (Pulse.Lib.CSharp.RefEq.ref_eq x y) {
    rewrite (O.raw y vy 1.0R) as (O.raw x vy 1.0R);
    B.to_ref_pts_to x #1.0R #vx;
    B.to_ref_pts_to x #1.0R #vy;
    R.gather (B.box_to_ref x);
    R.pts_to_perm_bound (B.box_to_ref x);
    unreachable ();
  }
}

ghost fn rec apart_cell (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
    (v: N.class_Node__raw a)
  preserves O.owns t 1.0R ** O.raw x v 1.0R
  ensures pure (~ (L.memP x (P.nboxes t)))
  decreases t
{
  match t {
    T.Leaf -> {}
    T.Branch l e r -> {
      unfold (O.owns t 1.0R);
      cells_distinct x (fst e) v
        {N.fld_Item = fst (snd e); N.fld_Color = O.color (snd (snd e));
         N.fld_Left = P.top l; N.fld_Right = P.top r};
      apart_cell l x v;
      apart_cell r x v;
      fold (O.owns t 1.0R);
    }
  }

}

ghost fn rec apart (#a: Type0) (t u: O.tree a)
  preserves O.owns t 1.0R ** O.owns u 1.0R
  ensures pure (RT.disjoint (P.nboxes t) (P.nboxes u))
  decreases t
{
  match t {
    T.Leaf -> {}
    T.Branch l e r -> {
      unfold (O.owns t 1.0R);
      apart_cell u (fst e)
        {N.fld_Item = fst (snd e); N.fld_Color = O.color (snd (snd e));
         N.fld_Left = P.top l; N.fld_Right = P.top r};
      apart l u;
      apart r u;
      fold (O.owns t 1.0R);
    }
  }
}

ghost fn rec facts (#a: Type0) (t: O.tree a)
  preserves O.owns t 1.0R
  ensures pure (O.good t)
  decreases t
{
  match t {
    T.Leaf -> {}
    T.Branch l e r -> {
      unfold (O.owns t 1.0R);
      B.pts_to_not_null (fst e);
      apart_cell l (fst e)
        {N.fld_Item = fst (snd e); N.fld_Color = O.color (snd (snd e));
         N.fld_Left = P.top l; N.fld_Right = P.top r};
      apart_cell r (fst e)
        {N.fld_Item = fst (snd e); N.fld_Color = O.color (snd (snd e));
         N.fld_Left = P.top l; N.fld_Right = P.top r};
      apart l r;
      facts l;
      facts r;
      RT.distinct_append (P.nboxes l) (P.nboxes r);
      fold (O.owns t 1.0R);
    }
  }
}
