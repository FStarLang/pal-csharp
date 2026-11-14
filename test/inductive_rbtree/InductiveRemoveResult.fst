module InductiveRemoveResult
#lang-pulse

open Pulse.Lib.Pervasives
module I = InductiveRemove
module C = InductiveCursor
module H = InductiveOwnership
module M = InductiveModel
module Q = InductiveOrder
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove
module U = Pulse.Lib.CSharp.TopDownSucc
module P = Pulse.Lib.CSharp.RegionPath
module N = Class_RbNode
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module S = Pulse.Lib.CSharp.Sorted
module O = Pulse.Lib.CSharp.Order
module B = Pulse.Lib.Box
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

ghost fn null_detached (#a: Type0) (x: N.class_RbNode__opt a)
  requires pure (x == B.null)
  ensures H.detached x
{
  rewrite emp as (H.detached x);
}

let after (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (par gp mt pom: N.class_RbNode__opt a) =
  C.good n /\
  (mt == B.null <==> S.key_index c ks k < 0) /\
  (if B.is_null mt then D.ok c (R.removed c ks k) n
   else U.rpre c ks k n mt pom par gp /\ par =!= B.null)

let end_search (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (par gp mt pom: N.class_RbNode__opt a) (found: bool)
  : Lemma (requires I.inv c ks k n B.null par gp mt pom found)
    (ensures after c ks k n par gp mt pom)
  = let (fs,s) = R.rdesc_elim c k n B.null par gp mt pom found in
    (match s with
     | T.Branch _ _ _ -> D.ok_focus c ks fs s
     | T.Leaf -> ());
    if B.is_null mt then R.end_none c ks k fs s B.null par gp mt pom found
    else (
      U.end_found c ks k fs s B.null par gp mt pom found;
      let _::rest = fs in
      P.mem_plug par fs s)

let complete (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a)
    (root: N.class_RbNode__opt a) (n: C.tree a) =
  root == P.top n /\ D.ok c (R.removed c ks k) n /\ ST.red_black (D.strip n)

let finish (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
  : Lemma (requires D.ok c (R.removed c ks k) n)
    (ensures complete c ks k (P.top n) (D.recolorn n false) /\
      InductiveMutation.recolor n (P.top n) false == D.recolorn n false)
  = D.finish c (R.removed c ks k) n;
    match n with
    | T.Leaf -> ()
    | T.Branch _ _ _ -> D.focus_at [] n

let semantic (#a: Type0) (c: O.comparer a) (t: M.tree a) (k: a) (u: M.tree a)
  : Lemma
    (requires S.strictly_sorted c (ST.keys t) /\ ST.keys u == R.removed c (ST.keys t) k)
    (ensures Q.removes_exactly c t k u /\
      T.size u == T.size t - (if ST.contains c t k then 1 else 0))
  = ST.contains_keys c t k;
    if not (ST.contains c t k) then Seq.lemma_eq_intro (ST.keys u) (ST.keys t)
    else (
      let s = ST.keys t in
      let i = S.key_index c s k in
      let pre = Seq.slice s 0 i in
      let post = Seq.slice s (i+1) (Seq.length s) in
      let pivot = Seq.index s i in
      assert (O.compare c k pivot == 0);
      Seq.lemma_eq_intro s (Seq.append pre (Seq.cons pivot post));
      Seq.lemma_eq_intro (ST.keys u) (Seq.append pre post);
      introduce exists (pre' post': Seq.seq a) (pivot': a).
        O.compare c k pivot' == 0 /\
        Seq.equal (ST.keys t) (Seq.append pre' (Seq.cons pivot' post')) /\
        Seq.equal (ST.keys u) (Seq.append pre' post')
      with pre post pivot and ())

unfold let labelled (#a: Type0) (root: N.class_RbNode__opt a) (c: O.comparer a)
    (ks: Seq.seq a) (k: a) =
  exists* (n: C.tree a). C.owns n ** pure (complete c ks k root n)

unfold let removed (#a: Type0) (root: N.class_RbNode__opt a) (c: O.comparer a)
    (t: M.tree a) (k: a) =
  exists* (u: M.tree a). H.holds root u **
    pure (ST.red_black u /\ S.strictly_sorted c (ST.keys u) /\
      ST.keys u == R.removed c (ST.keys t) k /\ Q.removes_exactly c t k u /\
      T.size u == T.size t - (if ST.contains c t k then 1 else 0))

ghost fn publish (#a: Type0) (root: N.class_RbNode__opt a) (c: O.comparer a)
    (t: M.tree a) (k: a)
  requires labelled root c (ST.keys t) k ** pure (S.strictly_sorted c (ST.keys t))
  ensures removed root c t k
{
  unfold (labelled root c (ST.keys t) k);
  with n. _;
  semantic c t k (D.strip n);
  C.unlabel n;
  rewrite (H.holds (P.top n) (D.strip n)) as (H.holds root (D.strip n));
  introduce exists* (u: M.tree a). H.holds root u **
    pure (ST.red_black u /\ S.strictly_sorted c (ST.keys u) /\
      ST.keys u == R.removed c (ST.keys t) k /\ Q.removes_exactly c t k u /\
      T.size u == T.size t - (if ST.contains c t k then 1 else 0))
    with (D.strip n);
}
