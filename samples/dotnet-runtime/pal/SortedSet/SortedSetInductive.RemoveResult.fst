module SortedSetInductive.RemoveResult

module I = SortedSetInductive.Remove
module C = SortedSetInductive.Ownership
module M = SortedSetInductive.Mutation
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove
module U = Pulse.Lib.CSharp.TopDownSucc
module P = Pulse.Lib.CSharp.RegionPath
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module S = Pulse.Lib.CSharp.Sorted
module O = Pulse.Lib.CSharp.Order
module B = Pulse.Lib.Box
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

let after (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (par gp mt pom: N.class_Node__opt a) =
  C.good n /\
  (mt == B.null <==> S.key_index c ks k < 0) /\
  (if B.is_null mt then D.ok c (R.removed c ks k) n
   else U.rpre c ks k n mt pom par gp /\ par =!= B.null)

let end_search (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (par gp mt pom: N.class_Node__opt a) (found: bool)
  : Lemma (requires I.inv c ks k n B.null par gp mt pom found)
    (ensures after c ks k n par gp mt pom /\ found == (mt =!= B.null))
  = let (fs,s) = R.rdesc_elim c k n B.null par gp mt pom found in
    (match s with
     | T.Branch _ _ _ -> D.ok_focus c ks fs s
     | T.Leaf -> ());
    if B.is_null mt then R.end_none c ks k fs s B.null par gp mt pom found
    else (
      U.end_found c ks k fs s B.null par gp mt pom found;
      let _::rest = fs in
      P.mem_plug par fs s)

let finish (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
  : Lemma (requires D.ok c (R.removed c ks k) n)
    (ensures D.ok c (R.removed c ks k) (D.recolorn n false) /\
      ST.red_black (D.strip (D.recolorn n false)) /\
      P.top (D.recolorn n false) == P.top n /\
      M.recolor n (P.top n) false == D.recolorn n false)
  = D.finish c (R.removed c ks k) n;
    match n with
    | T.Leaf -> ()
    | T.Branch _ _ _ -> D.focus_at [] n

let cardinality (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a)
  : Lemma (Seq.length (R.removed c ks k) ==
      Seq.length ks - (if S.key_index c ks k >= 0 then 1 else 0))
  = ()
