module InductiveRemove

module C = InductiveCursor
module N = Class_RbNode
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove
module P = Pulse.Lib.CSharp.RegionPath
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module B = Pulse.Lib.Box
module Seq = FStar.Seq
module M = InductiveMutation

#set-options "--z3rlimit 10"

let measure (#a: Type0) (n: C.tree a) (cur: N.class_RbNode__opt a) =
  T.size (P.sub n cur)
let inv (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool) =
  D.ok c ks n /\ R.rdesc c k n cur par gp mt pom found
let mid (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool) (m: int) =
  D.ok c ks n /\ R.mdesc c k n cur par gp mt pom found /\ measure n cur == m
let fixed (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par mt pom: N.class_RbNode__opt a) (found: bool) (m: int) =
  D.ok c ks n /\ R.fdesc c k n cur par mt pom found /\ measure n cur == m
let sibling (#a: Type0) (n: C.tree a) (par cur: N.class_RbNode__opt a) =
  let t = P.sub n par in
  if Pulse.Lib.CSharp.Region.eq_box (P.top (T.left t)) cur
  then P.top (T.right t) else P.top (T.left t)
let merged (#a: Type0) (n: C.tree a) (par: N.class_RbNode__opt a) =
  P.replace n par (D.merge2n (P.sub n par))
let order (#a: Type0) (c: O.comparer a) (k: a) (n: C.tree a)
    (cur: N.class_RbNode__opt a) (found: bool) =
  R.rord c k (P.sub n cur) found
let next (#a: Type0) (n: C.tree a) (cur: N.class_RbNode__opt a) (o: int) =
  P.top (R.rchild (P.sub n cur) o)

let start (#a: Type0) (c: O.comparer a) (k: a) (n: C.tree a)
  : Lemma (requires C.good n /\ ST.red_black (D.strip n) /\
      S.strictly_sorted c (ST.keys (D.strip n)))
    (ensures inv c (ST.keys (D.strip n)) k n (P.top n) B.null B.null B.null B.null false)
  = R.rdesc_intro c k [] n (P.top n) B.null B.null B.null B.null false

let path_facts (#a: Type0) (fs: list (C.frame a)) (s: C.tree a)
  : Lemma (requires C.good (P.plug fs s) /\ T.Branch? s)
    (ensures (
      let n = P.plug fs s in
      let cur = P.top s in
      let par = D.fb fs 0 in
      C.member n cur /\ cur =!= B.null /\ P.sub n cur == s /\
      D.parent_of n cur == par /\
      (par == B.null ==> fs == []) /\
      (par =!= B.null ==> C.member n par /\ D.parent_of n par == D.fb fs 1 /\
        sibling n par cur == P.top (InductiveRelink.sib fs))))
  = D.focus_at fs s;
    match fs with
    | [] -> ()
    | f::rest ->
      D.focus_at rest (P.fill f s);
      P.distinct_plug rest (P.fill f s);
      assert (D.all_nonnull (P.fill f s));
      assert (P.top s =!= P.top f.P.fsib)

let at_cur (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool)
  : Lemma (requires inv c ks k n cur par gp mt pom found /\ cur =!= B.null)
    (ensures C.good n /\ C.member n cur /\ D.parent_of n cur == par /\
      (par == B.null ==> cur == P.top n) /\
      (par =!= B.null ==> C.member n par /\ D.parent_of n par == gp))
  = let (fs,s) = R.rdesc_elim c k n cur par gp mt pom found in
    path_facts fs s

let not2 (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool)
  : Lemma (requires inv c ks k n cur par gp mt pom found /\ cur =!= B.null /\
      not (R.is2 (P.sub n cur)))
    (ensures fixed c ks k n cur par mt pom found (measure n cur))
  = R.fix_not2 c k n cur par gp mt pom found ks

let root (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool)
  : Lemma (requires inv c ks k n cur par gp mt pom found /\ cur =!= B.null /\
      par == B.null /\ R.is2 (P.sub n cur))
    (ensures fixed c ks k (M.recolor n cur true) cur par mt pom found (measure n cur))
  = let (fs,s) = R.rdesc_elim c k n cur par gp mt pom found in
    path_facts fs s;
    assert (fs == []);
    R.fix_root c ks k s cur par gp mt pom found

let direct (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool)
  : Lemma (requires inv c ks k n cur par gp mt pom found /\ cur =!= B.null /\
      par =!= B.null /\ R.is2 (P.sub n cur) /\
      not (D.nred (P.sub n (sibling n par cur))))
    (ensures mid c ks k n cur par gp mt pom found (measure n cur))
  = let (fs,s) = R.rdesc_elim c k n cur par gp mt pom found in
    path_facts fs s;
    let f::rest = fs in
    D.sub_top (({f with P.went_right=not f.P.went_right; P.fsib=s})::rest) f.P.fsib;
    R.fix_direct c ks k f rest s cur par gp mt pom found;
    R.mdesc_intro c k fs s cur par gp mt pom found

let merge (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool) (m: int)
  : Lemma (requires mid c ks k n cur par gp mt pom found m /\
      R.is2 (P.sub n (sibling n par cur)))
    (ensures fixed c ks k (merged n par) cur par mt pom found m /\
      P.top (merged n par) == P.top n)
  = let (fs,s) = R.mdesc_elim c k n cur par gp mt pom found in
    path_facts fs s;
    let f::rest = fs in
    D.focus_at rest (P.fill f s);
    D.sub_top (({f with P.went_right=not f.P.went_right; P.fsib=s})::rest) f.P.fsib;
    R.fix_merge c ks k f rest s cur par gp mt pom found;
    R.fdesc_intro c k (R.m_frame f::rest) (D.recolorn s true) cur par mt pom found;
    D.sub_top (R.m_frame f::rest) (D.recolorn s true);
    match rest with
    | [] -> ()
    | _::_ -> InductiveRelink.top_plug rest (P.fill f s) (D.merge2n (P.fill f s))

let advance (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par mt pom: N.class_RbNode__opt a) (found: bool) (m o: int)
  : Lemma (requires fixed c ks k n cur par mt pom found m /\ o == order c k n cur found)
    (ensures inv c ks k n (next n cur o) cur par (if o=0 then cur else mt)
       (if o=0 then par else pom) (found || o=0) /\
       0 <= measure n (next n cur o) /\ measure n (next n cur o) < m)
  = let (fs,s) = R.fdesc_elim c k n cur par mt pom found in
    path_facts fs s;
    R.step c ks k fs s cur par mt pom found;
    let fs' = R.rframe s o::fs in
    let s' = R.rchild s o in
    R.rdesc_intro c k fs' s' (P.top s') cur par (if o=0 then cur else mt)
      (if o=0 then par else pom) (found || o=0);
    D.sub_top fs' s'

let at_fixed (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par mt pom: N.class_RbNode__opt a) (found: bool) (m: int)
  : Lemma (requires fixed c ks k n cur par mt pom found m)
    (ensures C.good n /\ cur =!= B.null /\ C.member n cur)
  = let (fs,s) = R.fdesc_elim c k n cur par mt pom found in
    path_facts fs s
