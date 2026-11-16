module InductiveMutation
#lang-pulse

open Pulse.Lib.Pervasives
module C = InductiveCursor
module O = InductiveOwnership
module N = Class_RbNode
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let recolor (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) (red: bool) =
  if B.is_null x then n else P.replace n x (D.recolorn (P.sub n x) red)

ghost fn null_color (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) (red: bool)
  requires C.owns n ** pure (x == B.null)
  ensures C.owns (recolor n x red)
{
  rewrite (C.owns n) as (C.owns (recolor n x red));
}

unfold let color_opened (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) (red: bool) =
  exists* (k: a) (l r: N.class_RbNode__opt a).
    O.held x k red l r **
    C.owns (T.left (P.sub n x)) ** C.owns (T.right (P.sub n x)) **
    C.restore (fst (P.focus n x)) x **
    pure (T.Branch? (P.sub n x) /\ P.top (P.sub n x) == x /\
      k == D.nkey (P.sub n x) k /\
      l == P.top (T.left (P.sub n x)) /\ r == P.top (T.right (P.sub n x)))

ghost fn close_color (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) (red: bool)
  requires color_opened n x red ** pure (x =!= B.null)
  ensures C.owns (recolor n x red)
{
  unfold (color_opened n x red);
  with k l r. _;
  rewrite (O.held x k red l r) as
    (O.held x k red (P.top (T.left (P.sub n x))) (P.top (T.right (P.sub n x))));
  fold (C.owns (T.Branch (T.left (P.sub n x)) (x, (k, red)) (T.right (P.sub n x))));
  rewrite (C.owns (T.Branch (T.left (P.sub n x)) (x, (k, red)) (T.right (P.sub n x))))
    as (C.owns (D.recolorn (P.sub n x) red));
  rewrite (C.restore (fst (P.focus n x)) x) as
    (C.restore (fst (P.focus n x)) (P.top (D.recolorn (P.sub n x) red)));
  C.restore_focus (fst (P.focus n x)) (D.recolorn (P.sub n x) red);
  rewrite (C.owns (P.plug (fst (P.focus n x)) (D.recolorn (P.sub n x) red)))
    as (C.owns (recolor n x red));
}
