module SortedSetInductive.Walk

// A pending stack denotes subtrees of the immutable labelled snapshot. No heap
// interpretation, ownership map, or persistent borrow is needed for this model.
module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Cursor
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module W = Pulse.Lib.CSharp.RegionWalk
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq

#set-options "--z3rlimit 5"

let near (#a: Type0) (rev: bool) (t: T.tree a) =
  if rev then T.right t else T.left t

let far (#a: Type0) (rev: bool) (t: T.tree a) =
  if rev then T.left t else T.right t

let near_node (#a: Type0) (rev: bool) (t: O.tree a) (x: N.class_Node__opt a) =
  P.top (near rev (P.sub t x))

let far_node (#a: Type0) (rev: bool) (t: O.tree a) (x: N.class_Node__opt a) =
  P.top (far rev (P.sub t x))

let entry_value (#a: Type0) (t: O.tree a)
    (x: N.class_Node__opt a { O.good t /\ O.member t x }) : Tot (a & bool) =
  C.lookup_children t x;
  let T.Branch _ value _ = O.lookup t x in
  value

let entry (#a: Type0) (rev: bool) (t: O.tree a) (x: N.class_Node__opt a) =
  match O.lookup t x with
  | T.Leaf -> Seq.empty
  | T.Branch l (key, _) r ->
    Seq.cons key (W.okeys rev (if rev then l else r))

let rec pending (#a: Type0) (rev: bool) (t: O.tree a)
    (s: Seq.seq (N.class_Node__opt a)) : Tot (Seq.seq a) (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else
    let n = Seq.length s - 1 in
    Seq.append (entry rev t (Seq.index s n)) (pending rev t (Seq.slice s 0 n))

let walkable (#a: Type0) (t: O.tree a) (s: Seq.seq (N.class_Node__opt a)) =
  forall (i: nat). {:pattern Seq.index s i}
    i < Seq.length s ==> O.member t (Seq.index s i)

let empty (#a: Type0) (rev: bool) (t: O.tree a) (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires Seq.length s == 0)
      (ensures pending rev t s == Seq.empty /\ walkable t s)
  = ()

let push (#a: Type0) (rev: bool) (t: O.tree a)
    (s: Seq.seq (N.class_Node__opt a)) (x: N.class_Node__opt a)
  : Lemma (pending rev t (Seq.snoc s x) ==
           Seq.append (entry rev t x) (pending rev t s))
  = Seq.lemma_eq_intro (Seq.slice (Seq.snoc s x) 0 (Seq.length s)) s

let rec length (#a: Type0) (rev: bool) (t: O.tree a)
    (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires O.good t /\ walkable t s)
      (ensures Seq.length s <= Seq.length (pending rev t s))
      (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else
      let n = Seq.length s - 1 in
      C.lookup_children t (Seq.index s n);
      length rev t (Seq.slice s 0 n)

let descend (#a: Type0) (rev: bool) (t: O.tree a)
    (s: Seq.seq (N.class_Node__opt a)) (x: N.class_Node__opt a)
  : Lemma (requires O.good t /\ walkable t s /\ O.member t x)
      (ensures
        (let child = P.top (near rev (P.sub t x)) in
         (child =!= B.null ==> O.member t child) /\
         walkable t (Seq.snoc s x) /\
         Seq.length s < Seq.length (Seq.append (W.okeys rev (O.lookup t x)) (pending rev t s)) /\
         T.size (O.lookup t child) < T.size (O.lookup t x) /\
         Seq.append (W.okeys rev (O.lookup t x)) (pending rev t s) ==
         Seq.append (W.okeys rev (O.lookup t child)) (pending rev t (Seq.snoc s x))))
  = C.lookup_children t x;
    length rev t s;
    push rev t s x;
    let T.Branch l (key, _) r = O.lookup t x in
    if rev then
      Seq.append_assoc (W.okeys rev r) (Seq.cons key (W.okeys rev l)) (pending rev t s)
    else
      Seq.append_assoc (W.okeys rev l) (Seq.cons key (W.okeys rev r)) (pending rev t s)

let pop (#a: Type0) (rev: bool) (t: O.tree a)
    (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires O.good t /\ walkable t s /\ Seq.length s > 0)
      (ensures
        (let n = Seq.length s - 1 in
         let x = Seq.index s n in
         let child = P.top (far rev (P.sub t x)) in
         O.member t x /\ x =!= B.null /\
         walkable t (Seq.slice s 0 n) /\
         (child =!= B.null ==> O.member t child) /\
         (match O.lookup t x with
          | T.Leaf -> False
          | T.Branch _ (key, _) _ ->
            pending rev t s ==
              Seq.cons key (Seq.append (W.okeys rev (O.lookup t child))
                                       (pending rev t (Seq.slice s 0 n))))))
  = let n = Seq.length s - 1 in
    let x = Seq.index s n in
    C.lookup_children t x;
    let T.Branch l (key, _) r = O.lookup t x in
    let rest = pending rev t (Seq.slice s 0 n) in
    let keys = W.okeys rev (if rev then l else r) in
    Seq.lemma_eq_intro (Seq.append (Seq.cons key keys) rest)
                       (Seq.cons key (Seq.append keys rest))

let pop_at (#a: Type0) (rev: bool) (t: O.tree a)
    (s: Seq.seq (N.class_Node__opt a)) (ks: Seq.seq a) (n: int)
  : Lemma (requires O.good t /\ walkable t s /\ Seq.length s > 0 /\
                   0 <= n /\ n <= Seq.length ks /\
                   pending rev t s == Seq.slice ks n (Seq.length ks))
      (ensures
        (let m = Seq.length s - 1 in
         let x = Seq.index s m in
         let child = P.top (far rev (P.sub t x)) in
         O.member t x /\ x =!= B.null /\ n < Seq.length ks /\
         walkable t (Seq.slice s 0 m) /\
         (child =!= B.null ==> O.member t child) /\
         ST.keys (T.root_only (O.lookup t x)) == Seq.cons (Seq.index ks n) Seq.empty /\
         ST.root_key (O.lookup t x) (Seq.index ks n) == Seq.index ks n /\
         Seq.append (W.okeys rev (O.lookup t child))
                    (pending rev t (Seq.slice s 0 m)) ==
         Seq.slice ks (n + 1) (Seq.length ks)))
  = pop rev t s;
    let m = Seq.length s - 1 in
    let x = Seq.index s m in
    let child = P.top (far rev (P.sub t x)) in
    let T.Branch _ (key, _) _ = O.lookup t x in
    let rest = Seq.append (W.okeys rev (O.lookup t child))
                          (pending rev t (Seq.slice s 0 m)) in
    let window = Seq.slice ks n (Seq.length ks) in
    assert (Seq.index window 0 == Seq.index ks n);
    assert (key == Seq.index ks n);
    Seq.lemma_eq_intro (ST.keys (T.root_only (O.lookup t x))) (Seq.cons key Seq.empty);
    let at (i: nat { i < Seq.length rest })
      : Lemma (Seq.index rest i == Seq.index (Seq.slice ks (n + 1) (Seq.length ks)) i)
      = assert (Seq.index (Seq.cons key rest) (i + 1) == Seq.index rest i);
        assert (Seq.index window (i + 1) == Seq.index ks (n + 1 + i))
    in
    FStar.Classical.forall_intro at;
    Seq.lemma_eq_intro rest (Seq.slice ks (n + 1) (Seq.length ks))

let trace_step (#a: Type0) (keys: Seq.seq a)
    (before after: Seq.seq ((a & bool) & bool)) (result: bool)
  : Lemma (requires
      W.visited keys before /\ Seq.length before < Seq.length keys /\
      Seq.length after == Seq.length before + 1 /\
      Seq.slice after 0 (Seq.length before) == before /\
      fst (fst (Seq.index after (Seq.length before))) == Seq.index keys (Seq.length before) /\
      snd (Seq.index after (Seq.length before)) == result)
      (ensures (if result then W.visited keys after else W.walked keys after false))
  = let event = Seq.index after (Seq.length before) in
    Seq.lemma_eq_intro after (Seq.snoc before event);
    W.visited_snoc keys before event
