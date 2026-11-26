module SortedSetInductive.Read.Point
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Cursor
module I = SortedSetInductive.Read
module S = Class_SortedSet
module M = Struct_SortedSetModel
module N = Class_Node
module P = Pulse.Lib.CSharp.RegionPath
module T = Pulse.Lib.CSharp.Tree
module EQ = Pulse.Lib.CSharp.EqualityModel

#set-options "--z3rlimit 10"

unfold let tree_point (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (p: perm) =
  exists* (v: N.class_Node__raw a).
    O.raw x v p ** (O.raw x v p @==> O.owns t p) **
    pure (O.left v == P.top (T.left (P.sub t x)) /\
          O.right v == P.top (T.right (P.sub t x)))

unfold let any_tree_point (#a: Type0) (t: O.tree a) (p: perm) =
  exists* (x: N.class_Node__opt a). tree_point t x p

ghost fn open_tree (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires O.owns t p ** pure (O.good t /\ O.member t x)
  ensures tree_point t x p
{
  C.open_node t x p;
  unfold (C.window t x p);
  with key red l r. _;
  let v = { N.fld_Item=key; N.fld_Color=O.color red; N.fld_Left=l; N.fld_Right=r };
  rewrite (O.held x key red l r p) as (O.raw x v p);
  intro (O.raw x v p @==> O.owns t p)
    #(O.owns (T.left (P.sub t x)) p ** O.owns (T.right (P.sub t x)) p **
      C.context (fst (P.focus t x)) x p)
    fn _ {
      rewrite (O.raw x v p) as (O.held x key red l r p);
      C.close_node t x p;
    };
}

ghost fn close_tree (#a: Type0) (t: O.tree a) (p: perm)
  requires any_tree_point t p
  ensures O.owns t p
{
  unfold (any_tree_point t p);
  with x. _;
  unfold (tree_point t x p);
  with v. assert (O.raw x v p ** (O.raw x v p @==> O.owns t p));
  elim (O.raw x v p) (O.owns t p);
}

unfold let point (#a: Type0) {| equality_a: EQ.has_equality a |} (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (t: O.tree a) (x: N.class_Node__opt a) (p: perm) =
  exists* (v: N.class_Node__raw a).
    O.raw x v p ** (O.raw x v p @==> I.inv set m p) **
    pure (O.lookup t x ==
      T.Branch (O.lookup t v.N.fld_Left) (O.entry v) (O.lookup t v.N.fld_Right))

ghost fn open_set (#a: Type0) {| equality_a: EQ.has_equality a |} (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires I.inv set m p ** pure (t == m.M.fld_Labels /\ O.good t /\ O.member t x)
  ensures point set m t x p
{
  I.begin_set set m t p;
  C.open_node t x p;
  unfold (C.window t x p);
  with key red l r. _;
  let v = { N.fld_Item=key; N.fld_Color=O.color red; N.fld_Left=l; N.fld_Right=r };
  rewrite (O.held x key red l r p) as (O.raw x v p);
  intro (O.raw x v p @==> I.inv set m p)
    #(O.owns (T.left (P.sub t x)) p ** O.owns (T.right (P.sub t x)) p **
      C.context (fst (P.focus t x)) x p ** (O.owns t p @==> I.inv set m p))
    fn _ {
      rewrite (O.raw x v p) as (O.held x key red l r p);
      C.close_node t x p;
      elim (O.owns t p) (I.inv set m p);
    };
}

[@@pulse_intro; allow_ambiguous]
ghost fn close_return (#a: Type0) (#equality_a: EQ.has_equality a) (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (p: perm)
  requires exists* (x: N.class_Node__opt a) (v: N.class_Node__raw a).
    O.raw x v p ** (O.raw x v p @==> I.inv set m p)
  ensures S.class_SortedSet__inv set #p m
{
  with x v. assert (O.raw x v p ** (O.raw x v p @==> I.inv set m p));
  elim (O.raw x v p) (I.inv set m p);
  unfold (I.inv set m p);
}
