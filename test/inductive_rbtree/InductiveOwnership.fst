module InductiveOwnership
#lang-pulse

open Pulse
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module M = InductiveModel
module N = Class_RbNode

// Standard recursive separating conjunction: each child owns a disjoint tree.
// In particular no heap map, reachability axiom, or region is used.
let rec holds (#a: Type0) ([@@@mkey] root: N.class_RbNode__opt a) (t: M.tree a)
  : Tot slprop (decreases t) =
  match t with
  | T.Leaf -> pure (root == B.null)
  | T.Branch l e r ->
    exists* (v: N.class_RbNode__raw a).
      B.pts_to root v **
      pure (v.fld_key == fst e /\ v.fld_red == snd e) **
      holds v.fld_left l ** holds v.fld_right r

unfold let held (#a: Type0) (root: N.class_RbNode__opt a) (k: a) (red: bool)
    (l r: N.class_RbNode__opt a) : slprop =
  B.pts_to root { N.fld_key = k; N.fld_red = red; N.fld_left = l; N.fld_right = r }

unfold let opened (#a: Type0) (root: N.class_RbNode__opt a) (t: M.tree a) : slprop =
  exists* (k: a) (red: bool) (l r: N.class_RbNode__opt a).
    held root k red l r **
    holds l (M.left t) ** holds r (M.right t) **
    pure (t == M.node (M.left t) k red (M.right t))

ghost fn empty (#a: Type0) (u: unit)
  requires emp
  ensures holds (B.null #(N.class_RbNode__raw a)) (T.Leaf <: M.tree a)
{
  fold (holds (B.null #(N.class_RbNode__raw a)) (T.Leaf <: M.tree a));
}

ghost fn cases (#a: Type0) (root: N.class_RbNode__opt a) (t: M.tree a)
  preserves holds root t
  ensures pure (B.is_null root <==> T.Leaf? t)
{
  match t {
    T.Leaf -> { unfold (holds root t); fold (holds root t); }
    T.Branch l e r -> {
      unfold (holds root t);
      with v. assert (B.pts_to root v);
      B.pts_to_not_null root;
      fold (holds root t);
    }
  }
}

unfold let detached (#a: Type0) (root: N.class_RbNode__opt a) : slprop =
  if B.is_null root then emp
  else exists* (k: a) (red: bool). held root k red B.null B.null

ghost fn detach (#a: Type0) (root: N.class_RbNode__opt a) (key: a) (red: bool)
  requires held root key red B.null B.null
  ensures detached root
{
  B.pts_to_not_null root;
  assert (exists* (k: a) (red: bool). held root k red B.null B.null);
  rewrite (exists* (k: a) (red: bool). held root k red B.null B.null) as (detached root);
}

ghost fn open_tree (#a: Type0) (root: N.class_RbNode__opt a) (t: M.tree a)
  requires holds root t ** pure (not (T.Leaf? t))
  ensures opened root t ** pure (not (B.is_null root))
{
  rewrite (holds root t) as
    (holds root (T.Branch (M.left t) (T.Branch?._1 t) (M.right t)));
  unfold (holds root (T.Branch (M.left t) (T.Branch?._1 t) (M.right t)));
  with v. assert (B.pts_to root v);
  B.pts_to_not_null root;
  rewrite (B.pts_to root v) as
    (held root v.fld_key v.fld_red v.fld_left v.fld_right);
}

ghost fn close_tree (#a: Type0) (root: N.class_RbNode__opt a) (k: a) (red: bool)
    (l r: N.class_RbNode__opt a) (lt rt: M.tree a)
  requires held root k red l r ** holds l lt ** holds r rt
  ensures holds root (M.node lt k red rt)
{
  fold (holds root (T.Branch lt (k, red) rt));
  rewrite (holds root (T.Branch lt (k, red) rt)) as (holds root (M.node lt k red rt));
}
