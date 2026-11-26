module SortedSetInductive.RangeBreadth

module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Cursor
module W = SortedSetInductive.Walk
module Q = SortedSetInductive.Breadth
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module Ord = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module RW = Pulse.Lib.CSharp.RegionWalk
module R = Pulse.Lib.CSharp.RangeWalk
module SF = Pulse.Lib.CSharp.SetFilter
module Seq = FStar.Seq

#set-options "--z3rlimit 5"

let queue (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (q: Seq.seq (N.class_Node__opt a)) =
  W.walkable t q /\
  (forall (i: nat). {:pattern Seq.index q i} i < Seq.length q ==>
    S.strictly_sorted c (ST.keys (O.lookup t (Seq.index q i))))

let take_left (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo: a) (la: bool) (x: N.class_Node__opt a) =
  not (B.is_null (W.near_node false t x)) &&
  (not la || Ord.compare c lo (ST.root_key (O.lookup t x) lo) < 0)

let take_right (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (ua: bool) (x: N.class_Node__opt a) =
  not (B.is_null (W.far_node false t x)) &&
  (not ua || Ord.compare c hi (ST.root_key (O.lookup t x) lo) > 0)

let next (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (q: Seq.seq (N.class_Node__opt a) {Seq.length q > 0}) =
  let x = Seq.index q 0 in
  let rest = Seq.slice q 1 (Seq.length q) in
  let q1 = if take_left t c lo la x then Seq.snoc rest (W.near_node false t x) else rest in
  if take_right t c lo hi ua x then Seq.snoc q1 (W.far_node false t x) else q1

let queue_snoc (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (q: Seq.seq (N.class_Node__opt a)) (x: N.class_Node__opt a)
  : Lemma (requires queue t c q /\ O.member t x /\ S.strictly_sorted c (ST.keys (O.lookup t x)))
      (ensures queue t c (Seq.snoc q x))
  = assert (forall (i: nat). i < Seq.length q ==> Seq.index (Seq.snoc q x) i == Seq.index q i);
    assert (Seq.index (Seq.snoc q x) (Seq.length q) == x)

let start (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (x: N.class_Node__opt a)
    (q: Seq.seq (N.class_Node__opt a)) (keys: Seq.seq a) (tr: Seq.seq ((a & bool) & bool))
  : Lemma (requires O.good t /\ O.member t x /\ q == Seq.snoc Seq.empty x /\
      S.strictly_sorted c (ST.keys (O.lookup t x)) /\
      R.filter c lo hi la ua (ST.keys (O.lookup t x)) == keys /\ Seq.length tr == 0)
      (ensures queue t c q /\ W.walkable t q /\
        Seq.length (Q.pending t q) == T.size (O.lookup t x) /\
        RW.bf_visited keys tr (R.filter c lo hi la ua (Q.pending t q)))
  = Q.snoc t Seq.empty x;
    RW.okeys_fwd (O.lookup t x);
    Seq.append_empty_l (RW.okeys false (O.lookup t x));
    ST.keys_length (O.lookup t x);
    queue_snoc t c Seq.empty x;
    reveal_opaque (`%RW.bf_visited) (RW.bf_visited #a #bool)

let prune (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (x: N.class_Node__opt a)
  : Lemma (requires O.good t /\ O.member t x /\ S.strictly_sorted c (ST.keys (O.lookup t x)))
      (ensures
        (not (take_left t c lo la x) ==>
          R.filter c lo hi la ua (ST.keys (O.lookup t (W.near_node false t x))) == Seq.empty) /\
        (not (take_right t c lo hi ua x) ==>
          R.filter c lo hi la ua (ST.keys (O.lookup t (W.far_node false t x))) == Seq.empty))
  = C.lookup_root t;
    C.lookup_children t x;
    let T.Branch l (key, color) r = O.lookup t x in
    if la && Ord.compare c lo key >= 0 then R.prune_left c lo hi la ua l key color r;
    if ua && Ord.compare c hi key <= 0 then R.prune_right c lo hi la ua l key color r

let next_pending (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (q: Seq.seq (N.class_Node__opt a))
  : Lemma (requires O.good t /\ queue t c q /\ Seq.length q > 0)
      (ensures
        (let x = Seq.index q 0 in
         let l = W.near_node false t x in
         let r = W.far_node false t x in
         let rest = Seq.slice q 1 (Seq.length q) in
         O.member t x /\ x =!= B.null /\ queue t c rest /\
         (l =!= B.null ==> O.member t l) /\ (r =!= B.null ==> O.member t r) /\
         queue t c (next t c lo hi la ua q) /\
         R.filter c lo hi la ua (Q.pending t (next t c lo hi la ua q)) ==
           Seq.append
             (Seq.append (R.filter c lo hi la ua (Q.pending t rest))
               (R.filter c lo hi la ua (ST.keys (O.lookup t l))))
             (R.filter c lo hi la ua (ST.keys (O.lookup t r))) /\
         Seq.length (Q.pending t (next t c lo hi la ua q)) <=
           Seq.length (Q.pending t rest) + T.size (O.lookup t l) + T.size (O.lookup t r)))
  = let x = Seq.index q 0 in
    let rest = Seq.slice q 1 (Seq.length q) in
    assert (queue t c rest);
    C.lookup_root t;
    C.lookup_children t x;
    let T.Branch tl (key, color) tr = O.lookup t x in
    let l = W.near_node false t x in
    let r = W.far_node false t x in
    ST.sorted_branch c tl key color tr;
    prune t c lo hi la ua x;
    RW.okeys_fwd tl;
    RW.okeys_fwd tr;
    ST.keys_length tl;
    ST.keys_length tr;
    let br = Q.pending t rest in
    let kl = ST.keys tl in
    let kr = ST.keys tr in
    let fb = R.filter c lo hi la ua br in
    let fl = R.filter c lo hi la ua kl in
    let fr = R.filter c lo hi la ua kr in
    let el = take_left t c lo la x in
    let er = take_right t c lo hi ua x in
    let q1 = if el then Seq.snoc rest l else rest in
    let p1 = if el then Seq.append br kl else br in
    (if el then (Q.snoc t rest l; queue_snoc t c rest l));
    assert (Q.pending t q1 == p1);
    (if el then R.filter_append c lo hi la ua br kl else Seq.append_empty_r fb);
    assert (R.filter c lo hi la ua p1 == Seq.append fb fl);
    if er then (
      Q.snoc t q1 r;
      queue_snoc t c q1 r;
      R.filter_append c lo hi la ua p1 kr
    ) else Seq.append_empty_r (R.filter c lo hi la ua p1)

let dequeue (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (q: Seq.seq (N.class_Node__opt a))
    (keys: Seq.seq a) (tr: Seq.seq ((a & bool) & bool))
  : Lemma (requires O.good t /\ queue t c q /\ Seq.length q > 0 /\
      RW.bf_visited keys tr (R.filter c lo hi la ua (Q.pending t q)))
      (ensures
        (let x = Seq.index q 0 in
         let q' = next t c lo hi la ua q in
         O.member t x /\ x =!= B.null /\
         queue t c (Seq.slice q 1 (Seq.length q)) /\
         W.walkable t (Seq.slice q 1 (Seq.length q)) /\
         Seq.length (Q.pending t (Seq.slice q 1 (Seq.length q))) < Seq.length (Q.pending t q) /\
         queue t c q' /\ W.walkable t q' /\
         Seq.length q' <= Seq.length (Q.pending t q') /\
         Seq.length (Q.pending t q') < Seq.length (Q.pending t q) /\
         (ST.in_range c lo hi la ua (fst (W.entry_value t x)) ==>
           Seq.length tr < Seq.length keys /\
           RW.bf_visited keys (Seq.snoc tr (W.entry_value t x, true))
             (R.filter c lo hi la ua (Q.pending t q')) /\
           RW.bf_walked keys (Seq.snoc tr (W.entry_value t x, false)) false) /\
         (not (ST.in_range c lo hi la ua (fst (W.entry_value t x))) ==>
           RW.bf_visited keys tr (R.filter c lo hi la ua (Q.pending t q')))))
  = let x = Seq.index q 0 in
    let rest = Seq.slice q 1 (Seq.length q) in
    Q.front t q;
    next_pending t c lo hi la ua q;
    let q' = next t c lo hi la ua q in
    Q.length t q';
    C.lookup_children t x;
    RW.okeys_length false (O.lookup t x);
    assert (forall (i:nat). i < Seq.length rest ==> Seq.index rest i == Seq.index q (i + 1));
    assert (queue t c rest);
    let T.Branch tl (key, color) trr = O.lookup t x in
    RW.okeys_fwd (O.lookup t x);
    let kl = ST.keys tl in
    let kr = ST.keys trr in
    let br = Q.pending t rest in
    let fl = R.filter c lo hi la ua kl in
    let fr = R.filter c lo hi la ua kr in
    let fb = R.filter c lo hi la ua br in
    R.filter_append c lo hi la ua (Seq.append kl (Seq.cons key kr)) br;
    R.filter_append c lo hi la ua kl (Seq.cons key kr);
    R.filter_cons c lo hi la ua key kr;
    let fq = R.filter c lo hi la ua (Q.pending t q) in
    let fq' = R.filter c lo hi la ua (Q.pending t q') in
    if ST.in_range c lo hi la ua key then (
      RW.bf_step keys tr fl key fr fb (W.entry_value t x, true);
      RW.bf_step keys tr fl key fr fb (W.entry_value t x, false)
    ) else (
      let aux (y: a) : Lemma (SF.contains fq y <==> SF.contains fq' y) =
        SF.contains_append (Seq.append fl fr) fb y;
        SF.contains_append fl fr y;
        SF.contains_append (Seq.append fb fl) fr y;
        SF.contains_append fb fl y in
      FStar.Classical.forall_intro aux;
      R.bf_visited_perm keys tr fq fq'
    )
