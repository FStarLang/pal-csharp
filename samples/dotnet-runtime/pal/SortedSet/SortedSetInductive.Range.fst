module SortedSetInductive.Range

module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Cursor
module W = SortedSetInductive.Walk
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module Ord = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module RW = Pulse.Lib.CSharp.RegionWalk
module R = Pulse.Lib.CSharp.RangeWalk
module Seq = FStar.Seq
module I32 = FStar.Int32

#set-options "--z3rlimit 5"

let walkable (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (s: Seq.seq (N.class_Node__opt a)) =
  forall (i: nat). {:pattern Seq.index s i} i < Seq.length s ==>
    O.member t (Seq.index s i) /\
    ST.in_range c lo hi la ua (ST.root_key (O.lookup t (Seq.index s i)) lo) /\
    S.strictly_sorted c (ST.keys (O.lookup t (Seq.index s i)))

let empty (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires Seq.length s == 0)
      (ensures walkable t c lo hi la ua s /\ W.walkable t s /\ W.pending false t s == Seq.empty)
  = ()

let start (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (x: N.class_Node__opt a)
    (s: Seq.seq (N.class_Node__opt a)) (keys: Seq.seq a)
  : Lemma (requires Seq.length s == 0 /\
      R.filter c lo hi la ua (ST.keys (O.lookup t x)) == keys)
      (ensures R.filter c lo hi la ua
        (Seq.append (RW.okeys false (O.lookup t x)) (W.pending false t s)) == keys)
  = empty t c lo hi la ua s;
    RW.okeys_fwd (O.lookup t x);
    Seq.append_empty_r (RW.okeys false (O.lookup t x))

let push (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (s: Seq.seq (N.class_Node__opt a)) (x: N.class_Node__opt a)
  : Lemma (requires O.good t /\ walkable t c lo hi la ua s /\ O.member t x /\
                   ST.in_range c lo hi la ua (ST.root_key (O.lookup t x) lo) /\
                   S.strictly_sorted c (ST.keys (O.lookup t x)))
      (ensures walkable t c lo hi la ua (Seq.snoc s x) /\
               S.strictly_sorted c (ST.keys (O.lookup t (W.near_node false t x))))
  = C.lookup_children t x;
    let T.Branch l (key, color) r = O.lookup t x in
    ST.sorted_branch c l key color r;
    let extended = Seq.snoc s x in
    assert (forall (i: nat). i < Seq.length s ==> Seq.index extended i == Seq.index s i);
    assert (Seq.index extended (Seq.length s) == x)

let skip_right (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (x: N.class_Node__opt a) (rest: Seq.seq a)
  : Lemma (requires O.good t /\ O.member t x /\
                   la /\ I32.v (S.compare_i32 c lo (ST.root_key (O.lookup t x) lo)) > 0 /\
                   S.strictly_sorted c (ST.keys (O.lookup t x)))
      (ensures
        (let r = W.far_node false t x in
         (r =!= B.null ==> O.member t r) /\
         S.strictly_sorted c (ST.keys (O.lookup t r)) /\
         T.size (O.lookup t r) < T.size (O.lookup t x) /\
         R.filter c lo hi la ua (Seq.append (RW.okeys false (O.lookup t x)) rest) ==
         R.filter c lo hi la ua (Seq.append (RW.okeys false (O.lookup t r)) rest)))
  = C.lookup_children t x;
    let T.Branch l (key, color) r = O.lookup t x in
    ST.sorted_branch c l key color r;
    RW.okeys_fwd (O.lookup t x);
    RW.okeys_fwd r;
    R.skip_below c lo hi la ua l key color r rest

let skip_left (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (x: N.class_Node__opt a) (rest: Seq.seq a)
  : Lemma (requires O.good t /\ O.member t x /\
                   not (ST.in_range c lo hi la ua (ST.root_key (O.lookup t x) lo)) /\
                   not (la && I32.v (S.compare_i32 c lo (ST.root_key (O.lookup t x) lo)) > 0) /\
                   S.strictly_sorted c (ST.keys (O.lookup t x)))
      (ensures
        (let l = W.near_node false t x in
         (l =!= B.null ==> O.member t l) /\
         S.strictly_sorted c (ST.keys (O.lookup t l)) /\
         T.size (O.lookup t l) < T.size (O.lookup t x) /\
         R.filter c lo hi la ua (Seq.append (RW.okeys false (O.lookup t x)) rest) ==
         R.filter c lo hi la ua (Seq.append (RW.okeys false (O.lookup t l)) rest)))
  = C.lookup_children t x;
    let T.Branch l (key, color) r = O.lookup t x in
    ST.sorted_branch c l key color r;
    RW.okeys_fwd (O.lookup t x);
    RW.okeys_fwd l;
    R.skip_above c lo hi la ua l key color r rest

let pop_at (#a: Type0) (t: O.tree a) (c: Ord.comparer a)
    (lo hi: a) (la ua: bool) (s: Seq.seq (N.class_Node__opt a))
    (keys: Seq.seq a) (n: int)
  : Lemma (requires O.good t /\ Seq.length s > 0 /\ W.walkable t s /\
                   walkable t c lo hi la ua s /\ 0 <= n /\ n <= Seq.length keys /\
                   R.filter c lo hi la ua (W.pending false t s) == Seq.slice keys n (Seq.length keys))
      (ensures
        (let m = Seq.length s - 1 in
         let x = Seq.index s m in
         let rest = Seq.slice s 0 m in
         let r = W.far_node false t x in
         O.member t x /\ x =!= B.null /\ n < Seq.length keys /\
         W.walkable t rest /\ walkable t c lo hi la ua rest /\
         (r =!= B.null ==> O.member t r) /\
         S.strictly_sorted c (ST.keys (O.lookup t r)) /\
         ST.root_key (O.lookup t x) lo == Seq.index keys n /\
         Seq.length (RW.okeys false (O.lookup t r)) + Seq.length (W.pending false t rest) <
           Seq.length (W.pending false t s) /\
         R.filter c lo hi la ua (Seq.append (RW.okeys false (O.lookup t r)) (W.pending false t rest)) ==
           Seq.slice keys (n + 1) (Seq.length keys)))
  = W.pop false t s;
    let m = Seq.length s - 1 in
    let x = Seq.index s m in
    let rest = Seq.slice s 0 m in
    C.lookup_children t x;
    let T.Branch l (key, color) r = O.lookup t x in
    ST.sorted_branch c l key color r;
    let pending_rest = Seq.append (RW.okeys false (O.lookup t (W.far_node false t x)))
                                  (W.pending false t rest) in
    R.filter_cons c lo hi la ua key pending_rest;
    R.cons_window key (R.filter c lo hi la ua pending_rest) keys n
