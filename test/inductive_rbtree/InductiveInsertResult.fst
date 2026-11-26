module InductiveInsertResult
#lang-pulse

open Pulse.Lib.Pervasives
module I = InductiveInsert
module C = InductiveCursor
module H = InductiveOwnership
module M = InductiveModel
module Q = InductiveOrder
module D = Pulse.Lib.CSharp.TopDown
module N = Class_RbNode
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module S = Pulse.Lib.CSharp.Sorted
module O = Pulse.Lib.CSharp.Order
module B = Pulse.Lib.Box
module Seq = FStar.Seq
module CL = FStar.Classical

#set-options "--z3rlimit 10"

let every (#a: Type0) (p: a -> prop) (s: Seq.seq a) =
  forall (j: nat). j < Seq.length s ==> p (Seq.index s j)

let every_insert (#a: Type0) (p: a -> prop) (s: Seq.seq a) (i: nat{i <= Seq.length s}) (k: a)
  : Lemma (every p (D.seq_ins s i k) <==> (every p s /\ p k))
  = let u = D.seq_ins s i k in
    D.seq_ins_index s i k i;
    let fwd () : Lemma (requires every p u) (ensures every p s /\ p k) =
      let at (j: nat) : Lemma (j < Seq.length s ==> p (Seq.index s j)) =
        if j < i then D.seq_ins_index s i k j
        else D.seq_ins_index s i k (j+1)
      in CL.forall_intro at
    in
    let bwd () : Lemma (requires every p s /\ p k) (ensures every p u) =
      let at (j: nat) : Lemma (j < Seq.length u ==> p (Seq.index u j)) =
        D.seq_ins_index s i k j
      in CL.forall_intro at
    in
    CL.move_requires fwd ();
    CL.move_requires bwd ()

let semantic (#a: Type0) (c: O.comparer a) (t: M.tree a) (k: a) (u: M.tree a)
  : Lemma
    (requires S.strictly_sorted c (ST.keys t) /\ ST.keys u == I.expected c (ST.keys t) k)
    (ensures Q.adds_exactly c t k u /\
      T.size u == T.size t + (if ST.contains c t k then 0 else 1))
  = ST.contains_keys c t k;
    if ST.contains c t k then Seq.lemma_eq_intro (ST.keys u) (ST.keys t)
    else (
      let s = ST.keys t in
      let i = S.lower_bound c s k in
      D.seq_ins_index s i k i;
      let at (x: a) : Lemma (Q.member c u x <==> (Q.member c t x \/ O.compare c x k == 0)) =
        let p : a -> prop = fun y -> O.compare c x y <> 0 in
        Q.every_keys p t;
        Q.every_keys p u;
        every_insert p s i k
      in CL.forall_intro at)

unfold let labelled (#a: Type0) (root: N.class_RbNode__opt a) (c: O.comparer a)
    (ks: Seq.seq a) (k: a) =
  exists* (n: C.tree a). C.owns n ** pure (I.complete c ks k root n)

unfold let added (#a: Type0) (root: N.class_RbNode__opt a) (c: O.comparer a)
    (t: M.tree a) (k: a) =
  exists* (u: M.tree a). H.holds root u **
    pure (ST.red_black u /\ S.strictly_sorted c (ST.keys u) /\
      ST.keys u == I.expected c (ST.keys t) k /\ Q.adds_exactly c t k u /\
      T.size u == T.size t + (if ST.contains c t k then 0 else 1))

ghost fn publish (#a: Type0) (root: N.class_RbNode__opt a) (c: O.comparer a)
    (t: M.tree a) (k: a)
  requires labelled root c (ST.keys t) k ** pure (S.strictly_sorted c (ST.keys t))
  ensures added root c t k
{
  unfold (labelled root c (ST.keys t) k);
  with n. _;
  semantic c t k (D.strip n);
  C.unlabel n;
  rewrite (H.holds (Pulse.Lib.CSharp.RegionPath.top n) (D.strip n)) as (H.holds root (D.strip n));
  introduce exists* (u: M.tree a). H.holds root u **
    pure (ST.red_black u /\ S.strictly_sorted c (ST.keys u) /\
      ST.keys u == I.expected c (ST.keys t) k /\ Q.adds_exactly c t k u /\
      T.size u == T.size t + (if ST.contains c t k then 0 else 1))
    with (D.strip n);
}

ghost fn release_empty (#a: Type0) (n: C.tree a)
  requires C.owns n ** pure (C.good n /\ Pulse.Lib.CSharp.RegionPath.top n == B.null)
  ensures pure (n == T.Leaf)
{
  assert (pure (n == T.Leaf));
  rewrite (C.owns n) as emp;
}

let singleton (#a: Type0) (c: O.comparer a) (k: a) (x: N.class_RbNode__opt a)
  : Lemma (requires x =!= B.null)
    (ensures I.complete c (Seq.empty #a) k x (D.recolorn (D.leaf x k) false))
  = let s = Seq.empty #a in
    let n = D.recolorn (D.leaf x k) false in
    assert (S.key_index c s k < 0);
    assert (S.lower_bound c s k == 0);
    D.seq_ins_index s 0 k 0;
    assert (Seq.length (ST.keys (D.strip n)) == 1);
    Seq.lemma_eq_intro (ST.keys (D.strip n)) (I.expected c s k);
    assert (D.ok c (I.expected c s k) n);
    assert (ST.red_black (D.strip n))
