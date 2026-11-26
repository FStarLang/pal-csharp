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

// Ordinary C# field reads expose the owner before a proof operation. Closing
// it uses the actual raw record and its existing abstraction equality.
[@@pulse_intro]
ghost fn refold_owner (#a: Type0) (set: S.class_SortedSet a) (p: perm)
    (m: S.class_SortedSet__model a)
  requires exists* (r: S.class_SortedSet__raw a).
    B.pts_to set #p r ** O.owner r.S.fld_root r.S.fld_ownershipState p **
    pure (matches r.S.fld_root r.S.fld_ownershipState r.S.fld_comparer
      (FStar.Int32.v r.S.fld_count) (FStar.Int32.v r.S.fld_version) m)
  ensures S.class_SortedSet__inv set #p m
{
  fold (S.class_SortedSet__inv set #p m);
}

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

ghost fn node_facts (#a: Type0) (set: S.class_SortedSet a) (m: S.class_SortedSet__model a)
    (h: Q.observation a) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  preserves I.inv set m p
  requires pure (h == observation m /\ t == m.M.fld_Labels /\ (B.is_null x \/ O.member t x))
  ensures pure (Q.wf h x /\ Q.tree_at h x == O.lookup t x)
{
  unfold (I.inv set m p);
  unfold (S.class_SortedSet__inv set #p m);
  with r. _;
  SortedSetInductive.StateActive.active_node r.S.fld_ownershipState x;
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

// Short-circuit child reads may follow a call that already restored the owner.
[@@pulse_intro]
ghost fn auto_read (#a: Type0) (x: N.class_Node__opt a) (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a{Q.mem (observation m) x}) (p: perm)
  requires S.class_SortedSet__inv set #p m
  ensures B.pts_to x #p (Q.get (observation m) x) **
    (O.raw x (Q.get (observation m) x) p @==> I.inv set m p)
{
  fold (I.inv set m p);
  open_set set m (observation m) x p;
  unfold (window set m (observation m) x p);
  with v. _;
  rewrite (O.raw x v p) as (O.raw x (Q.get (observation m) x) p);
  rewrite (O.raw x v p @==> I.inv set m p)
    as (O.raw x (Q.get (observation m) x) p @==> I.inv set m p);
}

