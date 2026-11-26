module SortedSetInductive.ClonePop
#lang-pulse

open Pulse.Lib.Pervasives
module C = SortedSetInductive.Clone
module F = SortedSetInductive.CloneFocus
module O = SortedSetInductive.Ownership
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

let witness (a: Type0) = O.tree a & nat
let focus (#a: Type0) (w: witness a) = fst w
let offset (#a: Type0) (w: witness a) = snd w

noeq type frontier (a: Type0) = {
  lt: N.class_Node__opt a;
  rt: N.class_Node__opt a;
  lp: Seq.seq (C.pair a);
  rp: Seq.seq (C.pair a);
  ln: nat;
  rn: nat
}

// A proof phase records precisely the existential frontier just unpacked.
// Passing it to the next ghost call makes its fields ordinary proof parameters;
// no erased witness is ever used to control executable code.
let opened (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (pending: Seq.seq (C.pair a)) (remaining: nat) (p: perm) (f: frontier a) =
  match source with
  | T.Leaf -> pure False
  | T.Branch l e r ->
    O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p **
    O.held target (fst (snd e)) (snd (snd e)) f.lt f.rt 1.0R **
    C.cloning l f.lt f.lp f.ln p ** C.cloning r f.rt f.rp f.rn p **
    pure (pending == Seq.append f.lp f.rp /\ remaining == f.ln + f.rn)

let problem (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (pending: Seq.seq (C.pair a)) (remaining: nat) (p: perm) (phase: option (frontier a)) =
  match phase with
  | None -> C.cloning source target pending remaining p
  | Some f -> pure (T.Branch? source) ** opened source target pending remaining p f

ghost fn rec solve (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (prefix: Seq.seq (C.pair a)) (next: C.pair a) (remaining: nat) (p: perm)
    (phase: option (frontier a))
  requires problem source target (Seq.snoc prefix next) remaining p phase
  returns result: erased (O.tree a & nat)
  ensures C.todo (fst (reveal result)) (snd next) p **
    C.restore source target prefix (snd (reveal result)) (fst (reveal result)) (snd next) p **
    pure (T.Branch? (fst (reveal result)) /\ O.top (fst (reveal result)) == fst next /\
      remaining == snd (reveal result) + T.size (fst (reveal result)) /\
      Seq.length prefix <= snd (reveal result))
  decreases (2 * T.size source + (if None? phase then 1 else 0))
{
  match phase {
    None -> {
      unfold (problem source target (Seq.snoc prefix next) remaining p phase);
      C.facts source target (Seq.snoc prefix next) remaining p;
      assert (pure (T.Branch? source));
      let l = T.left source;
      let r = T.right source;
      let e = T.Branch?._1 source;
      let src = fst e;
      let key = fst (snd e);
      let red = snd (snd e);
      rewrite (C.cloning source target (Seq.snoc prefix next) remaining p) as
        (C.cloning (T.Branch l (src, (key, red)) r) target (Seq.snoc prefix next) remaining p);
      if (remaining = T.size source) {
        rewrite (C.cloning (T.Branch l (src, (key, red)) r) target (Seq.snoc prefix next) remaining p) as
          (C.waiting source target src key red (Seq.snoc prefix next) p);
        unfold (C.waiting source target src key red (Seq.snoc prefix next) p);
        Seq.lemma_eq_intro prefix Seq.empty;
        assert (pure (fst next == src /\ snd next == target));
        rewrite (O.owns source p) as (O.owns (T.Branch l (src, (key, red)) r) p);
        fold (C.todo (T.Branch l (src, (key, red)) r) target p);
        rewrite (C.todo (T.Branch l (src, (key, red)) r) target p) as (C.todo source (snd next) p);
        C.identity source target p;
        rewrite (C.restore source target Seq.empty 0 source target p) as
          (C.restore source target prefix 0 source (snd next) p);
        hide (source, 0)
      } else {
        C.open_expanded l r src target key red (Seq.snoc prefix next) remaining p;
        unfold (C.expanded l r src target key red (Seq.snoc prefix next) remaining p);
        with lt rt lp rp ln rn. _;
        let f = {lt=lt; rt=rt; lp=lp; rp=rp; ln=ln; rn=rn};
        rewrite (C.cloning l lt lp ln p) as (C.cloning l f.lt f.lp f.ln p);
        rewrite (C.cloning r rt rp rn p) as (C.cloning r f.rt f.rp f.rn p);
        fold (opened (T.Branch l (src, (key, red)) r) target (Seq.snoc prefix next) remaining p f);
        rewrite (opened (T.Branch l (src, (key, red)) r) target (Seq.snoc prefix next) remaining p f) as
          (opened source target (Seq.snoc prefix next) remaining p f);
        fold (problem source target (Seq.snoc prefix next) remaining p (Some f));
        solve source target prefix next remaining p (Some f)
      }
    }
    Some f -> {
      unfold (problem source target (Seq.snoc prefix next) remaining p phase);
      let l = T.left source;
      let r = T.right source;
      let e = T.Branch?._1 source;
      let src = fst e;
      let key = fst (snd e);
      let red = snd (snd e);
      rewrite (opened source target (Seq.snoc prefix next) remaining p f) as
        (opened (T.Branch l (src, (key, red)) r) target (Seq.snoc prefix next) remaining p f);
      unfold (opened (T.Branch l (src, (key, red)) r) target (Seq.snoc prefix next) remaining p f);
      if (Seq.length f.rp > 0) {
        C.facts l f.lt f.lp f.ln p;
        F.split_last f.lp f.rp prefix next;
        let before = Seq.slice f.rp 0 (Seq.length f.rp - 1);
        rewrite (C.cloning r f.rt f.rp f.rn p) as
          (C.cloning r f.rt (Seq.snoc before next) f.rn p);
        fold (problem r f.rt (Seq.snoc before next) f.rn p None);
        let found = solve r f.rt before next f.rn p None;
        let focus = fst (reveal found);
        let offset = snd (reveal found);
        rewrite (C.todo (fst (reveal found)) (snd next) p) as (C.todo focus (snd next) p);
        rewrite (C.restore r f.rt before (snd (reveal found)) (fst (reveal found)) (snd next) p) as
          (C.restore r f.rt before offset focus (snd next) p);
        F.lift_right l r src target f.lt f.rt key red f.lp before f.ln offset focus (snd next) p;
        rewrite (C.restore (T.Branch l (src, (key, red)) r) target
          (Seq.append f.lp before) (f.ln + offset) focus (snd next) p) as
          (C.restore source target prefix (f.ln + offset) focus (snd next) p);
        hide (focus, f.ln + offset)
      } else {
        C.facts r f.rt f.rp f.rn p;
        Seq.lemma_eq_intro f.rp Seq.empty;
        Seq.lemma_eq_intro f.lp (Seq.snoc prefix next);
        rewrite (C.cloning r f.rt f.rp f.rn p) as (C.cloning r f.rt Seq.empty 0 p);
        rewrite (C.cloning l f.lt f.lp f.ln p) as
          (C.cloning l f.lt (Seq.snoc prefix next) f.ln p);
        fold (problem l f.lt (Seq.snoc prefix next) f.ln p None);
        let found = solve l f.lt prefix next f.ln p None;
        let focus = fst (reveal found);
        let offset = snd (reveal found);
        rewrite (C.todo (fst (reveal found)) (snd next) p) as (C.todo focus (snd next) p);
        rewrite (C.restore l f.lt prefix (snd (reveal found)) (fst (reveal found)) (snd next) p) as
          (C.restore l f.lt prefix offset focus (snd next) p);
        F.lift_left l r src target f.lt f.rt key red prefix offset focus (snd next) p;
        rewrite (C.restore (T.Branch l (src, (key, red)) r) target prefix offset focus (snd next) p) as
          (C.restore source target prefix offset focus (snd next) p);
        hide (focus, offset)
      }
    }
  }
}

// The public witness comes solely from the resources indexed by the actual pop.
ghost fn pop (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (prefix: Seq.seq (C.pair a)) (next: C.pair a) (remaining: nat) (p: perm)
  requires C.cloning source target (Seq.snoc prefix next) remaining p
  returns result: erased (O.tree a & nat)
  ensures C.todo (fst (reveal result)) (snd next) p **
    C.restore source target prefix (snd (reveal result)) (fst (reveal result)) (snd next) p **
    pure (T.Branch? (fst (reveal result)) /\ O.top (fst (reveal result)) == fst next /\
      remaining == snd (reveal result) + T.size (fst (reveal result)) /\
      Seq.length prefix <= snd (reveal result) /\
      not (Pulse.Lib.Box.is_null (fst next)) /\ not (Pulse.Lib.Box.is_null (snd next)))
{
  fold (problem source target (Seq.snoc prefix next) remaining p None);
  let found = solve source target prefix next remaining p None;
  C.todo_facts (fst (reveal found)) (snd next) p;
  found
}
