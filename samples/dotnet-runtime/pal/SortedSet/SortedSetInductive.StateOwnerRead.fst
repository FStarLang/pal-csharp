module SortedSetInductive.StateOwnerRead
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
module O = SortedSetInductive.Ownership
module Q = SortedSetInductive.State
module R = SortedSetInductive.StateRead
module I = SortedSetInductive.Read
module S = Class_SortedSet
module M = Struct_SortedSetModel
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree

#set-options "--z3rlimit 10"

let observation (#a: Type0) (m: S.class_SortedSet__model a) = m.M.fld_Observation

// An opened owner may be re-abstracted by a readonly call. The loop preserves
// this observable model equality, NOT identity of its private retired witness.
let matches (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
    (c: Pulse.Lib.CSharp.Order.comparer a) (count version: int) (m: S.class_SortedSet__model a) =
  m == { M.fld_Tree=O.values (O.active s); M.fld_Comparer=c; M.fld_Count=count;
         M.fld_Version=version; M.fld_Root=root; M.fld_Labels=O.active s; M.fld_Observation=Q.observe s }

ghost fn root_facts (#a: Type0) (set: S.class_SortedSet a) (m: S.class_SortedSet__model a)
    (h: Q.observation a) (t: O.tree a) (p: perm)
  preserves I.inv set m p
  requires pure (h == observation m /\ t == m.M.fld_Labels)
  ensures pure (Q.wf h (O.top t) /\ Q.tree_at h (O.top t) == O.values t)
{
  unfold (I.inv set m p);
  unfold (S.class_SortedSet__inv set #p m);
  with r. _;
  SortedSetInductive.StateActive.active r.S.fld_ownershipState;
  fold (S.class_SortedSet__inv set #p m);
  fold (I.inv set m p);
}

unfold let window (#a: Type0) (set: S.class_SortedSet a) (m: S.class_SortedSet__model a)
    (h: Q.observation a) (x: N.class_Node__opt a) (p: perm) =
  exists* (v: N.class_Node__raw a).
    O.raw x v p ** (O.raw x v p @==> I.inv set m p) **
    pure (Q.find h x == Some v /\ not (B.is_null x) /\
      Q.tree_at h x == T.Branch (Q.tree_n (fst h) h (O.left v)) (O.entry v)
                               (Q.tree_n (fst h) h (O.right v)))

ghost fn open_set (#a: Type0) (set: S.class_SortedSet a) (m: S.class_SortedSet__model a)
    (h: Q.observation a) (x: N.class_Node__opt a) (p: perm)
  requires I.inv set m p ** pure (h == observation m /\ Q.mem h x)
  ensures window set m h x p
{
  unfold (I.inv set m p);
  unfold (S.class_SortedSet__inv set #p m);
  with r. _;
  R.open_owner r.S.fld_root r.S.fld_ownershipState x p;
  unfold (R.window r.S.fld_root r.S.fld_ownershipState x p);
  with v. _;
  B.pts_to_not_null x;
  Q.root_step h x;
  intro (O.raw x v p @==> I.inv set m p)
    #(B.pts_to set #p r ** (O.raw x v p @==> O.owner r.S.fld_root r.S.fld_ownershipState p))
    fn _ {
      elim (O.raw x v p) (O.owner r.S.fld_root r.S.fld_ownershipState p);
      fold (S.class_SortedSet__inv set #p m);
      fold (I.inv set m p);
    };
}

ghost fn close_set (#a: Type0) (set: S.class_SortedSet a) (m: S.class_SortedSet__model a)
    (h: Q.observation a) (x: N.class_Node__opt a) (p: perm)
  requires window set m h x p
  ensures I.inv set m p
{
  unfold (window set m h x p);
  with v. _;
  elim (O.raw x v p) (I.inv set m p);
}

// The unchanged C# `return _current.Item` closes this read window in the
// ordinary return epilogue. The captured raw owner/model is restored exactly.
[@@pulse_intro]
ghost fn close_return (#a: Type0) (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (p: perm)
  requires exists* (x: N.class_Node__opt a) (v: N.class_Node__raw a).
    O.raw x v p ** (O.raw x v p @==> I.inv set m p)
  ensures S.class_SortedSet__inv set #p m
{
  with x v. assert (O.raw x v p ** (O.raw x v p @==> I.inv set m p));
  elim (O.raw x v p) (I.inv set m p);
  unfold (I.inv set m p);
}
