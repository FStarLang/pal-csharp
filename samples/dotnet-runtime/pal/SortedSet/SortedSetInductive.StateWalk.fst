module SortedSetInductive.StateWalk

module Q = SortedSetInductive.State
module F = SortedSetInductive.StateFacts
module O = SortedSetInductive.Ownership
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module W = Pulse.Lib.CSharp.RegionWalk
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

let empty (#a: Type0) (rev: bool) (h: Q.observation a) (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires Seq.length s == 0)
      (ensures Seq.equal (Q.pending rev h s) Seq.empty /\ Q.walkable h s) = ()

let push (#a: Type0) (rev: bool) (h: Q.observation a)
    (s: Seq.seq (N.class_Node__opt a)) (x: N.class_Node__opt a)
  : Lemma (Q.pending rev h (Seq.snoc s x) == Seq.append (Q.entry rev h x) (Q.pending rev h s)) =
  Seq.lemma_eq_intro (Seq.slice (Seq.snoc s x) 0 (Seq.length s)) s

let rec length (#a: Type0) (rev: bool) (h: Q.observation a) (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires Q.walkable h s)
      (ensures Seq.length s <= Seq.length (Q.pending rev h s))
      (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else (
    let n = Seq.length s - 1 in
    F.step h (Seq.index s n);
    length rev h (Seq.slice s 0 n))

let descend (#a: Type0) (rev: bool) (h: Q.observation a)
    (s: Seq.seq (N.class_Node__opt a)) (x: N.class_Node__opt a)
  : Lemma (requires Q.wf h x /\ not (B.is_null x) /\ Q.walkable h s)
      (ensures Q.mem h x /\ T.Branch? (Q.tree_at h x) /\
        Q.wf h (F.near rev h x) /\ Q.wf h (F.far rev h x) /\
        Q.walkable h (Seq.snoc s x) /\
        T.size (Q.tree_at h (F.near rev h x)) < T.size (Q.tree_at h x) /\
        T.size (Q.tree_at h (F.far rev h x)) < T.size (Q.tree_at h x) /\
        Seq.length s < Seq.length (W.okeys rev (Q.tree_at h x)) + Seq.length (Q.pending rev h s) /\
        Seq.append (W.okeys rev (Q.tree_at h x)) (Q.pending rev h s) ==
          Seq.append (W.okeys rev (Q.tree_at h (F.near rev h x))) (Q.pending rev h (Seq.snoc s x))) =
  F.step h x;
  F.children rev h x;
  length rev h s;
  push rev h s x;
  let T.Branch l (k, _) r = Q.tree_at h x in
  if rev then Seq.append_assoc (W.okeys rev r) (Seq.cons k (W.okeys rev l)) (Q.pending rev h s)
  else Seq.append_assoc (W.okeys rev l) (Seq.cons k (W.okeys rev r)) (Q.pending rev h s)

let pop (#a: Type0) (rev: bool) (h: Q.observation a) (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires Seq.length s > 0 /\ Q.walkable h s)
      (ensures (
        let n = Seq.length s - 1 in
        let x = Seq.index s n in
        Q.mem h x /\ not (B.is_null x) /\ Q.wf h x /\
        Q.walkable h (Seq.slice s 0 n) /\ Q.wf h (F.far rev h x) /\
        Q.pending rev h s == Seq.cons (O.item (Q.get h x))
          (Seq.append (W.okeys rev (Q.tree_at h (F.far rev h x))) (Q.pending rev h (Seq.slice s 0 n))))) =
  let n = Seq.length s - 1 in
  let x = Seq.index s n in
  F.step h x;
  F.children rev h x;
  let T.Branch l (k, _) r = Q.tree_at h x in
  let rest = Q.pending rev h (Seq.slice s 0 n) in
  let o = W.okeys rev (if rev then l else r) in
  Seq.lemma_eq_intro (Seq.append (Seq.cons k o) rest) (Seq.cons k (Seq.append o rest))

let pop_at (#a: Type0) (rev: bool) (h: Q.observation a) (s: Seq.seq (N.class_Node__opt a))
    (ks: Seq.seq a) (n: int)
  : Lemma (requires Seq.length s > 0 /\ Q.walkable h s /\ 0 <= n /\ n <= Seq.length ks /\
        Q.pending rev h s == Seq.slice ks n (Seq.length ks))
      (ensures (
        let m = Seq.length s - 1 in
        let x = Seq.index s m in
        Q.mem h x /\ not (B.is_null x) /\ Q.wf h x /\ n < Seq.length ks /\
        Q.walkable h (Seq.slice s 0 m) /\ Q.wf h (F.far rev h x) /\
        O.item (Q.get h x) == Seq.index ks n /\
        Pulse.Lib.CSharp.SearchTree.root_key (Q.tree_at h x) (Seq.index ks n) == Seq.index ks n /\
        Seq.append (W.okeys rev (Q.tree_at h (F.far rev h x))) (Q.pending rev h (Seq.slice s 0 m)) ==
          Seq.slice ks (n + 1) (Seq.length ks))) =
  pop rev h s;
  let m = Seq.length s - 1 in
  let x = Seq.index s m in
  F.step h x;
  let rest = Seq.append (W.okeys rev (Q.tree_at h (F.far rev h x))) (Q.pending rev h (Seq.slice s 0 m)) in
  let k = O.item (Q.get h x) in
  let w = Seq.slice ks n (Seq.length ks) in
  assert (Seq.index w 0 == Seq.index ks n);
  let at (i: nat{i < Seq.length rest})
    : Lemma (Seq.index rest i == Seq.index (Seq.slice ks (n + 1) (Seq.length ks)) i) =
    assert (Seq.index (Seq.cons k rest) (i + 1) == Seq.index rest i);
    assert (Seq.index w (i + 1) == Seq.index ks (n + 1 + i)) in
  FStar.Classical.forall_intro at;
  Seq.lemma_eq_intro rest (Seq.slice ks (n + 1) (Seq.length ks))
