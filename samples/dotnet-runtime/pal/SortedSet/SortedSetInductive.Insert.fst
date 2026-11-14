module SortedSetInductive.Insert

module C = SortedSetInductive.Ownership
module N = Class_Node
module D = Pulse.Lib.CSharp.TopDown
module P = Pulse.Lib.CSharp.RegionPath
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module S = Pulse.Lib.CSharp.Sorted
module O = Pulse.Lib.CSharp.Order
module B = Pulse.Lib.Box
module Seq = FStar.Seq
module K = SortedSetInductive.Relink

#set-options "--z3rlimit 10"

let empty_keys (a: Type0) : Seq.seq a = Seq.empty
let black (#a: Type0) (n: C.tree a) = D.recolorn n false

let inserted (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) =
  D.seq_ins ks (S.lower_bound c ks k) k

let expected (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) =
  if S.key_index c ks k >= 0 then ks else inserted c ks k

let measure (#a: Type0) (c: O.comparer a) (k: a) (n: C.tree a) (cur: N.class_Node__opt a) =
  D.meas c k (P.sub n cur)

let inv (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp ggp: N.class_Node__opt a) (o: int) =
  T.Branch? n /\ D.ok c ks n /\ D.descent c k n cur par gp ggp o

let comparison (#a: Type0) (c: O.comparer a) (k: a) (n: C.tree a)
    (cur: N.class_Node__opt a) =
  D.cmp c k (D.nkey (P.sub n cur) k)

let ready (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp: N.class_Node__opt a) (o m: int) =
  T.Branch? n /\ D.ok c ks n /\ C.member n cur /\
  o == comparison c k n cur /\ o <> 0 /\
  D.descent c k n (D.next c k n cur) cur par gp o /\
  measure c k n (D.next c k n cur) < m

let split_tree (#a: Type0) (n: C.tree a) (cur: N.class_Node__opt a) =
  P.replace n cur (D.split4n (P.sub n cur))

let pending (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp ggp: N.class_Node__opt a) (o m: int) =
  D.balance_ready n cur par gp ggp /\
  ready c ks k (D.balance n cur) cur (if D.same_side n cur then par else ggp) gp o m

let split_result (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp ggp: N.class_Node__opt a) (o: int) =
  let n1 = split_tree n cur in
  C.good n1 /\ P.top n1 == P.top n /\ (par == B.null \/ C.member n1 par) /\
  (if D.nred (P.sub n1 par)
   then pending c ks k n1 cur par gp ggp o (measure c k n cur)
   else ready c ks k n1 cur par gp o (measure c k n cur))

let start (#a: Type0) (c: O.comparer a) (k: a) (n: C.tree a)
  : Lemma (requires C.good n /\ T.Branch? n /\ ST.red_black (D.strip n) /\
      S.strictly_sorted c (ST.keys (D.strip n)))
    (ensures inv c (ST.keys (D.strip n)) k n (P.top n) B.null B.null B.null 0)
  = D.descent_root c k n

let at_cur (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp ggp: N.class_Node__opt a) (o: int)
  : Lemma (requires inv c ks k n cur par gp ggp o /\ cur =!= B.null)
    (ensures C.member n cur)
  = let (fs, s) = D.descent_elim c k n cur par gp ggp o in
    D.ok_focus c ks fs s

let ready_intro (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp: N.class_Node__opt a) (o m: int)
  : Lemma (requires D.ok c ks n /\ cur =!= B.null /\
      D.descent c k n (D.next c k n cur) cur par gp o /\
      measure c k n (D.next c k n cur) < m)
    (ensures ready c ks k n cur par gp o m)
  = D.descent_next c ks k n (D.next c k n cur) cur par gp o

let look (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp ggp: N.class_Node__opt a) (o0 o: int)
  : Lemma (requires inv c ks k n cur par gp ggp o0 /\ cur =!= B.null /\
      o == comparison c k n cur)
    (ensures
      (o == 0 ==> S.key_index c ks k >= 0) /\
      (o <> 0 /\ not (D.is4 (P.sub n cur)) ==>
        ready c ks k n cur par gp o (measure c k n cur)))
  = if o = 0 then D.found c ks k n cur par gp ggp o0
    else if D.is4 (P.sub n cur) then ()
    else (
      D.step_plain c ks k n cur par gp ggp o0 o;
      D.meas_plain c ks k n cur par gp ggp o0 o;
      ready_intro c ks k n cur par gp o (measure c k n cur))

let split_step (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp ggp: N.class_Node__opt a) (o0 o: int)
  : Lemma (requires inv c ks k n cur par gp ggp o0 /\ cur =!= B.null /\
      o == comparison c k n cur /\ o <> 0 /\ D.is4 (P.sub n cur))
    (ensures split_result c ks k n cur par gp ggp o)
  = D.step_split c ks k n cur par gp ggp o0 o;
    D.meas_step_split c ks k n cur par gp ggp o0 o;
    at_cur c ks k n cur par gp ggp o0;
    P.focus_plug n cur;
    let fs, s = P.focus n cur in
    let n1 = split_tree n cur in
    assert (P.top (D.split4n s) == P.top s);
    if D.nred (P.sub n1 par) then
      ready_intro c ks k (D.balance n1 cur) cur
        (if D.same_side n1 cur then par else ggp) gp o (measure c k n cur)
    else ready_intro c ks k n1 cur par gp o (measure c k n cur);
    if par =!= B.null then (
      D.descent_next c ks k n cur par gp ggp o0;
      P.mem_plug par fs s;
      P.mem_plug par fs (D.split4n s));
    match fs with
    | [] -> ()
    | _::_ -> K.replace_top n cur (D.split4n s)

let at_end (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (par gp ggp: N.class_Node__opt a) (o: int)
  : Lemma (requires inv c ks k n B.null par gp ggp o)
    (ensures par =!= B.null /\ C.member n par /\
      (if o > 0 then T.right (P.sub n par) == T.Leaf else T.left (P.sub n par) == T.Leaf))
  = let (fs, s) = D.descent_elim c k n B.null par gp ggp o in
    (match s with
     | T.Branch _ _ _ -> D.ok_focus c ks fs s
     | T.Leaf -> ());
    let f0::rest = fs in
    P.mem_plug par fs s;
    D.focus_at rest (P.fill f0 s)

let linked_result (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (x par gp ggp: N.class_Node__opt a) (o: int) =
  let n1 = D.set_child n par (o > 0) (D.leaf x k) in
  S.key_index c ks k < 0 /\ P.top n1 == P.top n /\ C.good n1 /\ C.member n1 par /\
  (if D.nred (P.sub n1 par)
   then D.balance_ready n1 x par gp ggp /\ D.ok c (inserted c ks k) (D.balance n1 x)
   else D.ok c (inserted c ks k) n1)

let linked_leaf (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (x par gp ggp: N.class_Node__opt a) (o: int)
  : Lemma (requires inv c ks k n B.null par gp ggp o /\ x =!= B.null /\ not (C.member n x))
    (ensures linked_result c ks k n x par gp ggp o)
  = at_end c ks k n par gp ggp o;
    D.insert_leaf c ks k n par gp ggp o x;
    P.focus_plug n par;
    let fs,s = P.focus n par in
    let u = SortedSetInductive.Leaf.attach s (D.leaf x k) (o > 0) in
    assert (P.top u == par);
    P.mem_plug par fs u;
    match fs with
    | [] -> ()
    | _::_ -> K.replace_top n par u

let complete (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a)
    (root: N.class_Node__opt a) (n: C.tree a) =
  root == P.top n /\ D.ok c (expected c ks k) n /\ ST.red_black (D.strip n)

let finish (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
  : Lemma (requires D.ok c (expected c ks k) n)
    (ensures complete c ks k (P.top n) (D.recolorn n false))
  = D.finish c (expected c ks k) n

let balance_nodes (#a: Type0) (n: C.tree a) (cur par gp ggp: N.class_Node__opt a)
  : Lemma (requires D.balance_ready n cur par gp ggp)
    (ensures par =!= B.null /\ gp =!= B.null)
  = SortedSetInductive.Balance.layout n cur par gp ggp

let advance (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp next: N.class_Node__opt a) (o m: int)
  : Lemma (requires ready c ks k n cur par gp o m /\
      (o < 0 ==> next == P.top (T.left (P.sub n cur))) /\
      (o >= 0 ==> next == P.top (T.right (P.sub n cur))))
    (ensures inv c ks k n next cur par gp o /\ 0 <= measure c k n next /\ measure c k n next < m)
  = P.focus_plug n cur;
    assert (T.Branch? (P.sub n cur));
    assert (next == D.next c k n cur)

let singleton (#a: Type0) (c: O.comparer a) (k: a) (x: N.class_Node__opt a)
  : Lemma (requires x =!= B.null)
      (ensures complete c (Seq.empty #a) k x (black (D.leaf x k)))
  = let s = Seq.empty #a in
    let n = black (D.leaf x k) in
    assert (S.key_index c s k < 0);
    assert (S.lower_bound c s k == 0);
    D.seq_ins_index s 0 k 0;
    assert (Seq.length (ST.keys (D.strip n)) == 1);
    Seq.lemma_eq_intro (ST.keys (D.strip n)) (expected c s k);
    assert (D.ok c (expected c s k) n);
    assert (ST.red_black (D.strip n))

let result_facts (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a)
    (root: N.class_Node__opt a) (n: C.tree a)
  : Lemma (requires complete c ks k root n)
      (ensures C.good n /\ root == C.top n /\ ST.red_black (C.values n) /\
        S.strictly_sorted c (ST.keys (C.values n)) /\
        Seq.equal (ST.keys (C.values n)) (expected c ks k) /\
        T.size (C.values n) == Seq.length ks + (if S.key_index c ks k < 0 then 1 else 0))
  = ST.keys_length (C.values n);
    if S.key_index c ks k < 0 then D.seq_ins_index ks (S.lower_bound c ks k) k 0

let new_root (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
  : Lemma (requires D.ok c (expected c ks k) n /\ S.key_index c ks k < 0)
      (ensures P.top n =!= B.null /\ C.member n (P.top n))
  = D.seq_ins_index ks (S.lower_bound c ks k) k 0;
    match n with
    | T.Leaf -> ()
    | T.Branch _ _ _ -> ()
