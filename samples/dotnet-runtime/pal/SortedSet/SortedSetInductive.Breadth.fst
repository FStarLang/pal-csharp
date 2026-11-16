module SortedSetInductive.Breadth

module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Cursor
module W = SortedSetInductive.Walk
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module RW = Pulse.Lib.CSharp.RegionWalk
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq

#set-options "--z3rlimit 5"

// A FIFO queue denotes the concatenation of its labelled subtrees' keys.
let rec pending (#a: Type0) (t: O.tree a) (q: Seq.seq (N.class_Node__opt a))
  : Tot (Seq.seq a) (decreases Seq.length q) =
  if Seq.length q = 0 then Seq.empty
  else
    let n = Seq.length q - 1 in
    Seq.append (pending t (Seq.slice q 0 n))
               (RW.okeys false (O.lookup t (Seq.index q n)))

let snoc (#a: Type0) (t: O.tree a) (q: Seq.seq (N.class_Node__opt a)) (x: N.class_Node__opt a)
  : Lemma (pending t (Seq.snoc q x) ==
           Seq.append (pending t q) (RW.okeys false (O.lookup t x)))
  = Seq.lemma_eq_intro (Seq.slice (Seq.snoc q x) 0 (Seq.length q)) q

let rec front (#a: Type0) (t: O.tree a) (q: Seq.seq (N.class_Node__opt a))
  : Lemma (requires Seq.length q > 0)
      (ensures pending t q ==
        Seq.append (RW.okeys false (O.lookup t (Seq.index q 0)))
                   (pending t (Seq.slice q 1 (Seq.length q))))
      (decreases Seq.length q)
  = let n = Seq.length q - 1 in
    let first = RW.okeys false (O.lookup t (Seq.index q 0)) in
    if n = 0 then Seq.lemma_eq_intro (pending t q) (Seq.append first Seq.empty)
    else
      let init = Seq.slice q 0 n in
      front t init;
      let rest = Seq.slice q 1 (Seq.length q) in
      Seq.lemma_eq_intro (Seq.slice init 1 n) (Seq.slice rest 0 (n - 1));
      assert (Seq.index rest (n - 1) == Seq.index q n);
      Seq.append_assoc first (pending t (Seq.slice init 1 n))
                       (RW.okeys false (O.lookup t (Seq.index q n)))

let rec length (#a: Type0) (t: O.tree a) (q: Seq.seq (N.class_Node__opt a))
  : Lemma (requires O.good t /\ W.walkable t q)
      (ensures Seq.length q <= Seq.length (pending t q))
      (decreases Seq.length q)
  = if Seq.length q = 0 then ()
    else
      let n = Seq.length q - 1 in
      C.lookup_children t (Seq.index q n);
      length t (Seq.slice q 0 n)

let next (#a: Type0) (t: O.tree a)
    (q: Seq.seq (N.class_Node__opt a) { Seq.length q > 0 }) =
  let x = Seq.index q 0 in
  let l = W.near_node false t x in
  let r = W.far_node false t x in
  let rest = Seq.slice q 1 (Seq.length q) in
  let with_left = if B.is_null l then rest else Seq.snoc rest l in
  if B.is_null r then with_left else Seq.snoc with_left r

let next_pending (#a: Type0) (t: O.tree a)
    (q: Seq.seq (N.class_Node__opt a))
  : Lemma (requires O.good t /\ W.walkable t q /\ Seq.length q > 0)
      (ensures
        (let x = Seq.index q 0 in
         let l = W.near_node false t x in
         let r = W.far_node false t x in
         let rest = Seq.slice q 1 (Seq.length q) in
         O.member t x /\ x =!= B.null /\
         (l =!= B.null ==> O.member t l) /\
         (r =!= B.null ==> O.member t r) /\
         W.walkable t rest /\ W.walkable t (next t q) /\
         pending t (next t q) ==
           Seq.append (Seq.append (pending t rest) (RW.okeys false (O.lookup t l)))
                      (RW.okeys false (O.lookup t r))))
  = let x = Seq.index q 0 in
    let l = W.near_node false t x in
    let r = W.far_node false t x in
    let rest = Seq.slice q 1 (Seq.length q) in
    C.lookup_root t;
    C.lookup_children t x;
    let with_left = if B.is_null l then rest else Seq.snoc rest l in
    let left_keys = Seq.append (pending t rest) (RW.okeys false (O.lookup t l)) in
    (if B.is_null l then Seq.append_empty_r (pending t rest) else snoc t rest l);
    assert (pending t with_left == left_keys);
    if B.is_null r then Seq.append_empty_r left_keys else snoc t with_left r

let start (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
    (q: Seq.seq (N.class_Node__opt a)) (keys: Seq.seq a) (tr: Seq.seq ((a & bool) & bool))
  : Lemma (requires O.good t /\ x == O.top t /\ x =!= B.null /\
                   q == Seq.snoc Seq.empty x /\ keys == ST.keys (O.values t) /\ Seq.length tr == 0)
      (ensures W.walkable t q /\ RW.bf_visited keys tr (pending t q))
  = C.lookup_root t;
    snoc t Seq.empty x;
    reveal_opaque (`%RW.bf_visited) (RW.bf_visited #a #bool)

let dequeue (#a: Type0) (t: O.tree a) (q: Seq.seq (N.class_Node__opt a))
    (keys: Seq.seq a) (tr: Seq.seq ((a & bool) & bool))
  : Lemma (requires O.good t /\ W.walkable t q /\ Seq.length q > 0 /\
                   RW.bf_visited keys tr (pending t q))
      (ensures
        (let x = Seq.index q 0 in
         let rest = Seq.slice q 1 (Seq.length q) in
         let l = W.near_node false t x in
         let r = W.far_node false t x in
         O.member t x /\ x =!= B.null /\
         Seq.length tr < Seq.length keys /\
         Seq.length rest + (if B.is_null l then 0 else 1) + (if B.is_null r then 0 else 1)
             <= Seq.length keys - Seq.length tr - 1 /\
         Seq.length rest + Seq.length (RW.okeys false (O.lookup t l)) +
             Seq.length (RW.okeys false (O.lookup t r)) < Seq.length keys - Seq.length tr /\
         W.walkable t (next t q) /\
         RW.bf_visited keys (Seq.snoc tr (W.entry_value t x, true)) (pending t (next t q)) /\
         RW.bf_walked keys (Seq.snoc tr (W.entry_value t x, false)) false))
  = let x = Seq.index q 0 in
    let l = W.near_node false t x in
    let r = W.far_node false t x in
    let rest = Seq.slice q 1 (Seq.length q) in
    C.lookup_children t x;
    C.lookup_root t;
    front t q;
    length t rest;
    next_pending t q;
    let kl = RW.okeys false (O.lookup t l) in
    let kr = RW.okeys false (O.lookup t r) in
    let key = fst (W.entry_value t x) in
    RW.bf_step keys tr kl key kr (pending t rest) (W.entry_value t x, true);
    RW.bf_step keys tr kl key kr (pending t rest) (W.entry_value t x, false);
    if not (B.is_null l) then C.lookup_children t l;
    if not (B.is_null r) then C.lookup_children t r;
    reveal_opaque (`%RW.bf_visited) (RW.bf_visited #a #bool)
