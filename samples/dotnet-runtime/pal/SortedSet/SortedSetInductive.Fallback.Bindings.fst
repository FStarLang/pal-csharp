module SortedSetInductive.Fallback.Bindings

module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq
module N = Class_Node
module Own = SortedSetInductive.Ownership
module F = SortedSetInductive.Fallback
module Ref = SortedSetInductive.Fallback.Reference
module Count = SortedSetCount
module E = Pulse.Lib.CSharp.Equality
module H = HashSetChain
module R = Pulse.Lib.CSharp.Region

let seen (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a) (i: int) (nodes: Seq.seq (N.class_Node__opt a)) : prop =
  0 <= i /\ i <= Seq.length all /\
  F.seen_matches c (Count.ok_s c los his la ua) tree (Seq.slice all 0 i) nodes

let counts (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a) (i unique unfound: int) : prop =
  F.count_inv c (Count.ok_s c los his la ua) (ST.keys (Own.values tree)) all i unique unfound

let start (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a)
  : Lemma (ensures counts c los his la ua tree all 0 0 0 /\
                   seen c los his la ua tree all 0 Seq.empty)
  = F.count_start c (Count.ok_s c los his la ua) (ST.keys (Own.values tree)) all;
    F.seen_empty c (Count.ok_s c los his la ua) tree (Seq.slice all 0 0) Seq.empty

let step (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a) (i unique unfound: int)
  : Lemma
      (requires S.strictly_sorted c (ST.keys (Own.values tree)) /\ Count.bounded los his la ua /\
                counts c los his la ua tree all i unique unfound /\ i < Seq.length all)
      (ensures (let item = Seq.index all i in
                let present = Count.ok_s c los his la ua item &&
                              S.key_index c (ST.keys (Own.values tree)) item >= 0 in
                let found_before = Count.hit c (Seq.slice all 0 i) item in
                counts c los his la ua tree all (i + 1)
                  (unique + (if present && not found_before then 1 else 0))
                  (unfound + (if present then 0 else 1))))
  = Count.lookup_intro_s c (Own.values tree) los his la ua;
    F.count_loop_step c (Count.ok_s c los his la ua) (ST.keys (Own.values tree)) all i unique unfound

let lookup (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a) (i: int) (nodes: Seq.seq (N.class_Node__opt a))
    (node: N.class_Node__opt a) (item: a)
  : Lemma
      (requires S.strictly_sorted c (ST.keys (Own.values tree)) /\ Count.bounded los his la ua /\
                seen c los his la ua tree all i nodes /\ Own.member tree node /\
                O.compare c (ST.root_key (Own.lookup tree node) item) item == 0 /\
                Count.ok_s c los his la ua item)
      (ensures F.node_mem nodes node == Count.hit c (Seq.slice all 0 i) item)
  = Count.lookup_intro_s c (Own.values tree) los his la ua;
    Count.ok_equiv c (Count.ok_s c los his la ua) (ST.root_key (Own.lookup tree node) item) item;
    F.seen_lookup c (Count.ok_s c los his la ua) tree (Seq.slice all 0 i) nodes node item

let hit (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a) (i: int)
    (before after: Seq.seq (N.class_Node__opt a)) (node: N.class_Node__opt a)
  : Lemma
      (requires S.strictly_sorted c (ST.keys (Own.values tree)) /\
                seen c los his la ua tree all i before /\ i < Seq.length all /\
                Own.member tree node /\
                O.compare c (ST.root_key (Own.lookup tree node) (Seq.index all i)) (Seq.index all i) == 0 /\
                (forall (p: N.class_Node__opt a).
                  F.node_mem after p == (R.eq_box p node || F.node_mem before p)))
      (ensures seen c los his la ua tree all (i + 1) after)
  = Count.slice_snoc all i;
    F.seen_step c (Count.ok_s c los his la ua) tree (Seq.slice all 0 i) before after node (Seq.index all i)

let miss (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a) (i: int) (nodes: Seq.seq (N.class_Node__opt a))
  : Lemma
      (requires S.strictly_sorted c (ST.keys (Own.values tree)) /\ Count.bounded los his la ua /\
                seen c los his la ua tree all i nodes /\ i < Seq.length all /\
                not (Count.ok_s c los his la ua (Seq.index all i) &&
                     S.key_index c (ST.keys (Own.values tree)) (Seq.index all i) >= 0))
      (ensures seen c los his la ua tree all (i + 1) nodes)
  = Count.lookup_intro_s c (Own.values tree) los his la ua;
    Count.slice_snoc all i;
    F.seen_miss c (Count.ok_s c los his la ua) tree (Seq.slice all 0 i) nodes (Seq.index all i)

let done_ (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a) (i unique unfound: int) (stop: bool)
  : Lemma
      (requires counts c los his la ua tree all i unique unfound /\
                (i == Seq.length all \/ (stop /\ unfound > 0)))
      (ensures unfound >= 0 /\
               (unfound > 0 <==> Count.unfound_s c los his la ua (ST.keys (Own.values tree)) all > 0) /\
               (not stop \/ unfound == 0 ==>
                 unique == Count.found_s c los his la ua (ST.keys (Own.values tree)) all))
  = F.count_done c (Count.ok_s c los his la ua) (ST.keys (Own.values tree)) all i unique unfound stop

let finish (#a: Type0) (c: O.comparer a) (los his: Seq.seq a) (la ua: bool)
    (tree: Own.tree a) (all: Seq.seq a) (unique unfound: int) (stopped: bool)
  : Lemma
      (requires
        (stopped ==> unfound > 0 /\ Count.unfound_s c los his la ua (ST.keys (Own.values tree)) all > 0) /\
        (not stopped ==> counts c los his la ua tree all (Seq.length all) unique unfound))
      (ensures unfound >= 0 /\
        (unfound > 0 <==> Count.unfound_s c los his la ua (ST.keys (Own.values tree)) all > 0) /\
        (not stopped ==> unique == Count.found_s c los his la ua (ST.keys (Own.values tree)) all))
  = if not stopped then done_ c los his la ua tree all (Seq.length all) unique unfound false

let node_mem (a: Type0) (nodes: Seq.seq (N.class_Node__opt a)) (node: N.class_Node__opt a) =
  F.node_mem nodes node

let reference_mem (a: Type0) (comparer: option (E.comparer (N.class_Node__opt a)))
    (nodes: Seq.seq (N.class_Node__opt a)) (node: N.class_Node__opt a)
  : Lemma
      (requires H.same_equality #(N.class_Node__opt a) #(E.reference_equality (N.class_Node__raw a)) None comparer)
      (ensures H.mem #(N.class_Node__opt a) #(E.reference_equality (N.class_Node__raw a)) comparer nodes node
               <==> node_mem a nodes node)
  = Ref.mem comparer nodes node

let added (a: Type0) (before after: Seq.seq (N.class_Node__opt a)) (node: N.class_Node__opt a)
  : Lemma (requires H.added before after node)
          (ensures forall (p: N.class_Node__opt a).
            node_mem a after p == (R.eq_box p node || node_mem a before p))
  = Ref.added before after node

let unchanged (a: Type0) (nodes: Seq.seq (N.class_Node__opt a)) (node: N.class_Node__opt a)
  : Lemma (requires node_mem a nodes node)
          (ensures forall (p: N.class_Node__opt a).
            node_mem a nodes p == (R.eq_box p node || node_mem a nodes p))
  = Ref.unchanged nodes node

let default_after (a: Type0) (before after: option (E.comparer (N.class_Node__opt a)))
  : Lemma
      (requires
        H.same_equality #(N.class_Node__opt a) #(E.reference_equality (N.class_Node__raw a)) None before /\
        H.same_equality #(N.class_Node__opt a) #(E.reference_equality (N.class_Node__raw a)) before after)
      (ensures H.same_equality #(N.class_Node__opt a) #(E.reference_equality (N.class_Node__raw a)) None after)
  = ()
