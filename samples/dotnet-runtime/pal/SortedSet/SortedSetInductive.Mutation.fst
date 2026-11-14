module SortedSetInductive.Mutation
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module E = SortedSetInductive.Edit
module C = SortedSetInductive.Cursor
module N = Class_Node
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let recolor (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (red: bool) =
  if B.is_null x then n else P.replace n x (D.recolorn (P.sub n x) red)

let node_red (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) = D.nred (P.sub n x)

ghost fn null_color (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (red: bool)
  requires O.owns n 1.0R ** pure (x == B.null)
  ensures O.owns (recolor n x red) 1.0R
{
  rewrite (O.owns n 1.0R) as (O.owns (recolor n x red) 1.0R);
}

unfold let color_opened (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (red: bool) =
  exists* (v: N.class_Node__raw a).
    O.raw x v 1.0R **
    O.owns (T.left (P.sub n x)) 1.0R ** O.owns (T.right (P.sub n x)) 1.0R **
    E.restore (fst (P.focus n x)) x 1.0R **
    pure (T.Branch? (P.sub n x) /\ P.top (P.sub n x) == x /\
      v.N.fld_Color == O.color red /\ O.item v == D.nkey (P.sub n x) (O.item v) /\
      v.N.fld_Left == P.top (T.left (P.sub n x)) /\ v.N.fld_Right == P.top (T.right (P.sub n x)))

ghost fn open_color (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires O.owns n 1.0R ** pure (O.good n /\ O.member n x)
  ensures color_opened n x (node_red n x) ** pure (x =!= B.null)
{
  C.open_node n x 1.0R;
  unfold (C.window n x 1.0R);
  with k red l r. _;
  E.context_trade (fst (P.focus n x)) x 1.0R;
  rewrite (O.held x k red l r 1.0R) as (O.held x k (node_red n x) l r 1.0R);
}

ghost fn close_color (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (red: bool)
  requires color_opened n x red ** pure (x =!= B.null)
  ensures O.owns (recolor n x red) 1.0R
{
  unfold (color_opened n x red);
  with v. _;
  rewrite (O.raw x v 1.0R) as
    (O.held x (O.item v) red (P.top (T.left (P.sub n x))) (P.top (T.right (P.sub n x))) 1.0R);
  fold (O.owns (T.Branch (T.left (P.sub n x)) (x, (O.item v, red)) (T.right (P.sub n x))) 1.0R);
  rewrite (O.owns (T.Branch (T.left (P.sub n x)) (x, (O.item v, red)) (T.right (P.sub n x))) 1.0R)
    as (O.owns (D.recolorn (P.sub n x) red) 1.0R);
  rewrite (E.restore (fst (P.focus n x)) x 1.0R) as
    (E.restore (fst (P.focus n x)) (P.top (D.recolorn (P.sub n x) red)) 1.0R);
  E.restore_focus (fst (P.focus n x)) (D.recolorn (P.sub n x) red) 1.0R;
  rewrite (O.owns (P.plug (fst (P.focus n x)) (D.recolorn (P.sub n x) red)) 1.0R)
    as (O.owns (recolor n x red) 1.0R);
}
