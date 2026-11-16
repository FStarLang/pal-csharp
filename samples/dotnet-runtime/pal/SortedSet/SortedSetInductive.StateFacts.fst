module SortedSetInductive.StateFacts

module Q = SortedSetInductive.State
module O = SortedSetInductive.Ownership
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree

#set-options "--z3rlimit 10"

let rec monotone (#a: Type0) (m n: nat) (h: Q.observation a) (x: N.class_Node__opt a)
  : Lemma (requires Q.closed m h x /\ m <= n)
      (ensures Q.closed n h x /\ Q.tree_n m h x == Q.tree_n n h x)
      (decreases m) =
  if B.is_null x then ()
  else (
    let r = Q.get h x in
    monotone (m - 1) (n - 1) h (O.left r);
    monotone (m - 1) (n - 1) h (O.right r))

let null (#a: Type0) (h: Q.observation a) (x: N.class_Node__opt a)
  : Lemma (requires B.is_null x)
      (ensures Q.wf h x /\ Q.tree_at h x == T.Leaf) =
  reveal_opaque (`%Q.wf) (Q.wf #a);
  reveal_opaque (`%Q.tree_at) (Q.tree_at #a)

let step (#a: Type0) (h: Q.observation a) (x: N.class_Node__opt a)
  : Lemma (requires Q.wf h x /\ not (B.is_null x))
      (ensures Q.mem h x /\
        Q.wf h (O.left (Q.get h x)) /\ Q.wf h (O.right (Q.get h x)) /\
        Q.tree_at h x ==
          T.Branch (Q.tree_at h (O.left (Q.get h x))) (O.entry (Q.get h x))
                   (Q.tree_at h (O.right (Q.get h x)))) =
  reveal_opaque (`%Q.wf) (Q.wf #a);
  reveal_opaque (`%Q.tree_at) (Q.tree_at #a);
  let r = Q.get h x in
  monotone (Q.fuel h - 1) (Q.fuel h) h (O.left r);
  monotone (Q.fuel h - 1) (Q.fuel h) h (O.right r)

let near (#a: Type0) (rev: bool) (h: Q.observation a) (x: N.class_Node__opt a) =
  match Q.find h x with
  | None -> B.null
  | Some r -> if rev then O.right r else O.left r

let far (#a: Type0) (rev: bool) (h: Q.observation a) (x: N.class_Node__opt a) =
  match Q.find h x with
  | None -> B.null
  | Some r -> if rev then O.left r else O.right r

let children (#a: Type0) (rev: bool) (h: Q.observation a) (x: N.class_Node__opt a)
  : Lemma (requires Q.wf h x /\ not (B.is_null x))
      (ensures Q.mem h x /\ Q.wf h (near rev h x) /\ Q.wf h (far rev h x) /\
        Q.tree_at h (near rev h x) == (if rev then T.right (Q.tree_at h x) else T.left (Q.tree_at h x)) /\
        Q.tree_at h (far rev h x) == (if rev then T.left (Q.tree_at h x) else T.right (Q.tree_at h x)) /\
        T.size (Q.tree_at h (near rev h x)) < T.size (Q.tree_at h x) /\
        T.size (Q.tree_at h (far rev h x)) < T.size (Q.tree_at h x)) =
  step h x

