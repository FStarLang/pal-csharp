module SortedSetInductive.CloneState
#lang-pulse

open Pulse.Lib.Pervasives
module C = SortedSetInductive.Clone
module S = SortedSetInductive.CloneStep
module O = SortedSetInductive.Ownership
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

let budget = erased nat
let value (b: budget) = reveal b
let initial (#a: Type0) (source: O.tree a) : Tot budget = hide (T.size source)
let previous (b: budget) : Tot budget =
  hide (if value b > 0 then value b - 1 else 0)

ghost fn start (#a: Type0) (source: O.tree a) (src target: N.class_Node a)
    (pending: Seq.seq (C.pair a)) (remaining: budget) (p: perm)
  requires C.cloning source target (S.jobs src target) (T.size source) p **
    pure (Seq.length pending == 1 /\ Seq.index pending 0 == (src, target) /\
      value remaining == T.size source)
  ensures C.cloning source target pending (value remaining) p
{
  Seq.lemma_eq_intro pending (S.jobs src target);
  rewrite (C.cloning source target (S.jobs src target) (T.size source) p) as
    (C.cloning source target pending (value remaining) p);
}

ghost fn finish_task (#a: Type0) (source: O.tree a) (root: N.class_Node__opt a)
    (focus: O.tree a) (target: N.class_Node__opt a)
    (prefix pending: Seq.seq (C.pair a)) (offset: nat) (before: budget) (p: perm)
  requires C.restore source root prefix offset focus target p **
    S.complete focus target prefix pending p **
    pure (value before == offset + T.size focus)
  ensures C.cloning source root pending (value (previous before)) p
{
  match focus {
    T.Leaf -> {
      unfold (S.complete focus target prefix pending p);
      assert (pure False);
    }
    T.Branch l e r -> {
      rewrite (S.complete focus target prefix pending p) as
        (S.complete (T.Branch l e r) target prefix pending p);
      unfold (S.complete (T.Branch l e r) target prefix pending p);
      with lt rt. _;
      C.join l r (fst e) target lt rt (fst (snd e)) (snd (snd e))
        (S.jobs (O.top l) lt) (S.jobs (O.top r) rt) (T.size l) (T.size r) p;
      rewrite (C.cloning (T.Branch l (fst e, (fst (snd e), snd (snd e))) r) target
        (Seq.append (S.jobs (O.top l) lt) (S.jobs (O.top r) rt)) (T.size l + T.size r) p) as
        (C.cloning focus target
          (Seq.append (S.jobs (O.top l) lt) (S.jobs (O.top r) rt)) (T.size l + T.size r) p);
      C.resume source root prefix offset focus target
        (Seq.append (S.jobs (O.top l) lt) (S.jobs (O.top r) rt)) (T.size l + T.size r) p;
      Seq.append_assoc prefix (S.jobs (O.top l) lt) (S.jobs (O.top r) rt);
      rewrite (C.cloning source root
        (Seq.append prefix (Seq.append (S.jobs (O.top l) lt) (S.jobs (O.top r) rt)))
        (offset + (T.size l + T.size r)) p) as
        (C.cloning source root pending (value (previous before)) p);
    }
  }
}
