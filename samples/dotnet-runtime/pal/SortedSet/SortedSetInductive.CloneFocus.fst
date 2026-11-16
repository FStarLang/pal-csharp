module SortedSetInductive.CloneFocus
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Forall.Util
open Pulse.Lib.Trade.Util
module C = SortedSetInductive.Clone
module O = SortedSetInductive.Ownership
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

ghost fn lift_right (#a: Type0) (l r: O.tree a) (src target lt rt: N.class_Node__opt a)
    (key: a) (red: bool) (lp prefix: Seq.seq (C.pair a)) (ln offset: nat)
    (focus: O.tree a) (destination: N.class_Node__opt a) (p: perm)
  requires O.held src key red (O.top l) (O.top r) p **
    O.held target key red lt rt 1.0R **
    C.cloning l lt lp ln p ** C.restore r rt prefix offset focus destination p
  ensures C.restore (T.Branch l (src, (key, red)) r) target
    (Seq.append lp prefix) (ln + offset) focus destination p
{
  intro (forall* (work: Seq.seq (C.pair a) & nat).
    C.cloning focus destination (fst work) (snd work) p @==>
    C.cloning (T.Branch l (src, (key, red)) r) target
      (Seq.append (Seq.append lp prefix) (fst work)) ((ln + offset) + snd work) p)
    #(O.held src key red (O.top l) (O.top r) p **
      O.held target key red lt rt 1.0R **
      C.cloning l lt lp ln p ** C.restore r rt prefix offset focus destination p)
    fn _ work {
      C.resume r rt prefix offset focus destination (fst work) (snd work) p;
      C.join l r src target lt rt key red lp (Seq.append prefix (fst work))
        ln (offset + snd work) p;
      Seq.append_assoc lp prefix (fst work);
      rewrite (C.cloning (T.Branch l (src, (key, red)) r) target
        (Seq.append lp (Seq.append prefix (fst work))) (ln + (offset + snd work)) p)
        as (C.cloning (T.Branch l (src, (key, red)) r) target
          (Seq.append (Seq.append lp prefix) (fst work)) ((ln + offset) + snd work) p);
    };
  fold (C.restore (T.Branch l (src, (key, red)) r) target
    (Seq.append lp prefix) (ln + offset) focus destination p);
}

ghost fn lift_left (#a: Type0) (l r: O.tree a) (src target lt rt: N.class_Node__opt a)
    (key: a) (red: bool) (prefix: Seq.seq (C.pair a)) (offset: nat)
    (focus: O.tree a) (destination: N.class_Node__opt a) (p: perm)
  requires O.held src key red (O.top l) (O.top r) p **
    O.held target key red lt rt 1.0R **
    C.cloning r rt Seq.empty 0 p ** C.restore l lt prefix offset focus destination p
  ensures C.restore (T.Branch l (src, (key, red)) r) target prefix offset focus destination p
{
  intro (forall* (work: Seq.seq (C.pair a) & nat).
    C.cloning focus destination (fst work) (snd work) p @==>
    C.cloning (T.Branch l (src, (key, red)) r) target
      (Seq.append prefix (fst work)) (offset + snd work) p)
    #(O.held src key red (O.top l) (O.top r) p **
      O.held target key red lt rt 1.0R **
      C.cloning r rt Seq.empty 0 p ** C.restore l lt prefix offset focus destination p)
    fn _ work {
      C.resume l lt prefix offset focus destination (fst work) (snd work) p;
      C.join l r src target lt rt key red (Seq.append prefix (fst work)) Seq.empty
        (offset + snd work) 0 p;
      Seq.lemma_eq_intro (Seq.append (Seq.append prefix (fst work)) Seq.empty)
        (Seq.append prefix (fst work));
      rewrite (C.cloning (T.Branch l (src, (key, red)) r) target
        (Seq.append (Seq.append prefix (fst work)) Seq.empty) ((offset + snd work) + 0) p)
        as (C.cloning (T.Branch l (src, (key, red)) r) target
          (Seq.append prefix (fst work)) (offset + snd work) p);
    };
  fold (C.restore (T.Branch l (src, (key, red)) r) target prefix offset focus destination p);
}

let split_last (#a: Type0) (lp rp prefix: Seq.seq (C.pair a)) (next: C.pair a)
  : Lemma
      (requires Seq.append lp rp == Seq.snoc prefix next /\ Seq.length rp > 0)
      (ensures (
        let before = Seq.slice rp 0 (Seq.length rp - 1) in
        rp == Seq.snoc before next /\ prefix == Seq.append lp before))
  = let before = Seq.slice rp 0 (Seq.length rp - 1) in
    assert (Seq.length (Seq.append lp rp) == Seq.length lp + Seq.length rp);
    assert (Seq.length (Seq.snoc prefix next) == Seq.length prefix + 1);
    assert (Seq.length prefix + 1 == Seq.length lp + Seq.length rp);
    assert (Seq.index (Seq.snoc prefix next) (Seq.length prefix) == next);
    assert (Seq.index (Seq.append lp rp) (Seq.length prefix) ==
      Seq.index rp (Seq.length rp - 1));
    assert (Seq.index rp (Seq.length rp - 1) == next);
    Seq.lemma_eq_intro rp (Seq.snoc before next);
    let at (i: nat { i < Seq.length prefix })
      : Lemma (Seq.index prefix i == Seq.index (Seq.append lp before) i)
      = assert (Seq.index prefix i == Seq.index (Seq.snoc prefix next) i);
        assert (Seq.index prefix i == Seq.index (Seq.append lp rp) i);
        if i >= Seq.length lp then
          assert (Seq.index before (i - Seq.length lp) == Seq.index rp (i - Seq.length lp)) in
    FStar.Classical.forall_intro at;
    Seq.lemma_eq_intro prefix (Seq.append lp before)
