module SortedSetInductive.Clone
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Forall.Util
open Pulse.Lib.Trade.Util
module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Construction
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

let pair (a: Type0) = N.class_Node__opt a & N.class_Node__opt a

unfold let waiting (#a: Type0) (source: O.tree a) (target src: N.class_Node__opt a)
    (key: a) (red: bool) (pending: Seq.seq (pair a)) (p: perm) =
  O.owns source p **
  O.held target key red B.null B.null 1.0R **
  pure (Seq.length pending == 1 /\
    fst (Seq.index pending 0) == src /\ snd (Seq.index pending 0) == target)

// The stack is the left-to-right frontier of this recursive construction.
// An unexpanded node owns the entire immutable source subtree and just one
// fresh destination cell. An expanded node owns both roots and recursively
// owns its two construction problems. There is no heap map or region token.
let rec cloning (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (pending: Seq.seq (pair a)) (remaining: nat) (p: perm)
    : Tot slprop (decreases source) =
  match source with
  | T.Leaf ->
    pure (target == B.null /\ Seq.length pending == 0 /\ remaining == 0)
  | T.Branch l e r ->
      let src = fst e in
      let key = fst (snd e) in
      let red = snd (snd e) in
      if remaining = T.size source then
        waiting source target src key red pending p
      else
        exists* (lt rt: N.class_Node__opt a)
            (lp rp: Seq.seq (pair a)) (ln rn: nat).
          O.held src key red (O.top l) (O.top r) p **
          O.held target key red lt rt 1.0R **
          cloning l lt lp ln p ** cloning r rt rp rn p **
          pure (pending == Seq.append lp rp /\ remaining == ln + rn)

unfold let expanded (#a: Type0) (l r: O.tree a)
    (src target: N.class_Node__opt a) (key: a) (red: bool)
    (pending: Seq.seq (pair a)) (remaining: nat) (p: perm) =
  exists* (lt rt: N.class_Node__opt a)
      (lp rp: Seq.seq (pair a)) (ln rn: nat).
    O.held src key red (O.top l) (O.top r) p **
    O.held target key red lt rt 1.0R **
    cloning l lt lp ln p ** cloning r rt rp rn p **
    pure (pending == Seq.append lp rp /\ remaining == ln + rn)

ghost fn open_expanded (#a: Type0) (l r: O.tree a)
    (src target: N.class_Node__opt a) (key: a) (red: bool)
    (pending: Seq.seq (pair a)) (remaining: nat) (p: perm)
  requires cloning (T.Branch l (src, (key, red)) r) target pending remaining p **
    pure (remaining <> T.size (T.Branch l (src, (key, red)) r))
  ensures expanded l r src target key red pending remaining p
{
  unfold (cloning (T.Branch l (src, (key, red)) r) target pending remaining p);
  rewrite (if remaining = T.size (T.Branch l (src, (key, red)) r)
    then waiting (T.Branch l (src, (key, red)) r) target src key red pending p
    else expanded l r src target key red pending remaining p)
    as (expanded l r src target key red pending remaining p);
}

ghost fn close_expanded (#a: Type0) (l r: O.tree a)
    (src target: N.class_Node__opt a) (key: a) (red: bool)
    (pending: Seq.seq (pair a)) (remaining: nat) (p: perm)
  requires expanded l r src target key red pending remaining p **
    pure (remaining <> T.size (T.Branch l (src, (key, red)) r))
  ensures cloning (T.Branch l (src, (key, red)) r) target pending remaining p
{
  rewrite (expanded l r src target key red pending remaining p) as
    (if remaining = T.size (T.Branch l (src, (key, red)) r)
     then waiting (T.Branch l (src, (key, red)) r) target src key red pending p
     else expanded l r src target key red pending remaining p);
  fold (cloning (T.Branch l (src, (key, red)) r) target pending remaining p);
}

ghost fn empty (#a: Type0) (p: perm)
  requires emp
  ensures cloning (T.Leaf <: O.tree a) B.null Seq.empty 0 p
{
  fold (cloning (T.Leaf <: O.tree a) B.null Seq.empty 0 p);
}

ghost fn seed (#a: Type0) (l r: O.tree a) (src target: N.class_Node a)
    (key: a) (red: bool) (p: perm)
  requires O.owns (T.Branch l (src, (key, red)) r) p **
    O.fresh target key (O.color red)
  ensures cloning (T.Branch l (src, (key, red)) r) target
    (Seq.create 1 (src, target)) (T.size (T.Branch l (src, (key, red)) r)) p
{
  rewrite (O.fresh target key (O.color red)) as
    (O.held target key red B.null B.null 1.0R);
  fold (waiting (T.Branch l (src, (key, red)) r) target src key red (Seq.create 1 (src, target)) p);
  rewrite (waiting (T.Branch l (src, (key, red)) r) target src key red (Seq.create 1 (src, target)) p)
    as (cloning (T.Branch l (src, (key, red)) r) target
      (Seq.create 1 (src, target)) (T.size (T.Branch l (src, (key, red)) r)) p);
}

ghost fn rec facts (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (pending: Seq.seq (pair a)) (remaining: nat) (p: perm)
  preserves cloning source target pending remaining p
  ensures pure (Seq.length pending <= remaining /\ remaining <= T.size source /\
    (Seq.length pending == 0 <==> remaining == 0))
  decreases source
{
  match source {
    T.Leaf -> {
      unfold (cloning source target pending remaining p);
      fold (cloning source target pending remaining p);
    }
    T.Branch l e r -> {
      rewrite (cloning source target pending remaining p) as
        (cloning (T.Branch l e r) target pending remaining p);
      let src = fst e;
      let key = fst (snd e);
      let red = snd (snd e);
      rewrite (cloning (T.Branch l e r) target pending remaining p) as
        (cloning (T.Branch l (src, (key, red)) r) target pending remaining p);
      if (remaining <> T.size (T.Branch l e r)) {
        open_expanded l r src target key red pending remaining p;
        unfold (expanded l r src target key red pending remaining p);
        with lt rt lp rp ln rn. _;
        facts l lt lp ln p;
        facts r rt rp rn p;
        fold (expanded l r src target key red pending remaining p);
        close_expanded l r src target key red pending remaining p;
        rewrite (cloning (T.Branch l (src, (key, red)) r) target pending remaining p) as
          (cloning source target pending remaining p);
      } else {
        rewrite (cloning (T.Branch l (src, (key, red)) r) target pending remaining p) as
          (waiting source target src key red pending p);
        unfold (waiting source target src key red pending p);
        fold (waiting source target src key red pending p);
        rewrite (waiting source target src key red pending p) as
          (cloning source target pending remaining p);
      };
    }
  }
}

// At an empty frontier, recursively return every source permission and the
// complete destination ownership, with exact item/color/shape correspondence.
ghost fn rec finish (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (pending: Seq.seq (pair a)) (remaining: nat) (p: perm)
  requires cloning source target pending remaining p ** pure (Seq.length pending == 0)
  ensures O.owns source p ** C.holds target (O.values source) 1.0R
  decreases source
{
  match source {
    T.Leaf -> {
      unfold (cloning source target pending remaining p);
      fold (O.owns source p);
      C.empty target 1.0R;
    }

    T.Branch l e r -> {
      rewrite (cloning source target pending remaining p) as
        (cloning (T.Branch l e r) target pending remaining p);
      let src = fst e;
      let key = fst (snd e);
      let red = snd (snd e);
      rewrite (cloning (T.Branch l e r) target pending remaining p) as
        (cloning (T.Branch l (src, (key, red)) r) target pending remaining p);
      if (remaining <> T.size (T.Branch l e r)) {
        open_expanded l r src target key red pending remaining p;
        unfold (expanded l r src target key red pending remaining p);
        with lt rt lp rp ln rn. _;
        finish l lt lp ln p;
        finish r rt rp rn p;
        fold (O.owns (T.Branch l (src, (key, red)) r) p);
        fold (C.holds target (T.Branch (O.values l) (key, red) (O.values r)) 1.0R);
        rewrite (O.owns (T.Branch l (src, (key, red)) r) p) as (O.owns source p);
        rewrite (C.holds target (T.Branch (O.values l) (key, red) (O.values r)) 1.0R) as
          (C.holds target (O.values source) 1.0R);
      } else {
        rewrite (cloning (T.Branch l (src, (key, red)) r) target pending remaining p) as
          (waiting source target src key red pending p);
        unfold (waiting source target src key red pending p);
        assert (pure False);
      }
    }
  }
}

ghost fn join (#a: Type0) (l r: O.tree a) (src target lt rt: N.class_Node__opt a)
    (key: a) (red: bool) (lp rp: Seq.seq (pair a)) (ln rn: nat) (p: perm)
  requires O.held src key red (O.top l) (O.top r) p **
    O.held target key red lt rt 1.0R **
    cloning l lt lp ln p ** cloning r rt rp rn p
  ensures cloning (T.Branch l (src, (key, red)) r) target
    (Seq.append lp rp) (ln + rn) p
{
  facts l lt lp ln p;
  facts r rt rp rn p;
  fold (expanded l r src target key red (Seq.append lp rp) (ln + rn) p);
  close_expanded l r src target key red (Seq.append lp rp) (ln + rn) p;
}

// A popped task owns exactly the unexpanded source subtree and its fresh copy.
let todo (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a) (p: perm) =
  match source with
  | T.Leaf -> pure False
  | T.Branch _ e _ ->
    O.owns source p ** O.held target (fst (snd e)) (snd (snd e)) B.null B.null 1.0R

ghost fn todo_facts (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a) (p: perm)
  preserves todo source target p
  ensures pure (not (B.is_null (O.top source)) /\ not (B.is_null target))
{
  match source {
    T.Leaf -> {
      unfold (todo source target p);
      fold (todo source target p);
    }
    T.Branch l e r -> {
      unfold (todo source target p);
      unfold (O.owns source p);
      unfold (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p);
      unfold (O.held target (fst (snd e)) (snd (snd e)) B.null B.null 1.0R);
      B.pts_to_not_null (fst e);
      B.pts_to_not_null target;
      fold (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p);
      fold (O.held target (fst (snd e)) (snd (snd e)) B.null B.null 1.0R);
      fold (O.owns source p);
      fold (todo source target p);
    }
  }
}

// The enclosing recursive construction remains owned in this checked trade.
// Completing the focus restores the fixed root with its actual updated frontier.
let restore (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (prefix: Seq.seq (pair a)) (offset: nat)
    (focus: O.tree a) (destination: N.class_Node__opt a) (p: perm) =
  forall* (work: Seq.seq (pair a) & nat).
    cloning focus destination (fst work) (snd work) p @==>
    cloning source target (Seq.append prefix (fst work)) (offset + snd work) p

ghost fn resume (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (prefix: Seq.seq (pair a)) (offset: nat)
    (focus: O.tree a) (destination: N.class_Node__opt a)
    (pending: Seq.seq (pair a)) (remaining: nat) (p: perm)
  requires restore source target prefix offset focus destination p **
    cloning focus destination pending remaining p
  ensures cloning source target (Seq.append prefix pending) (offset + remaining) p
{
  unfold (restore source target prefix offset focus destination p);
  Pulse.Lib.Forall.Util.elim #_ #(fun work ->
    cloning focus destination (fst work) (snd work) p @==>
    cloning source target (Seq.append prefix (fst work)) (offset + snd work) p)
    (pending, remaining);
  Pulse.Lib.Trade.Util.elim _ _;
}

ghost fn identity (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a) (p: perm)
  requires emp
  ensures restore source target Seq.empty 0 source target p
{
  intro (forall* (work: Seq.seq (pair a) & nat).
    cloning source target (fst work) (snd work) p @==>
    cloning source target (Seq.append Seq.empty (fst work)) (0 + snd work) p)
    #emp fn _ work {
      Seq.lemma_eq_intro (Seq.append Seq.empty (fst work)) (fst work);
      rewrite (cloning source target (fst work) (snd work) p) as
        (cloning source target (Seq.append Seq.empty (fst work)) (0 + snd work) p);
    };
  fold (restore source target Seq.empty 0 source target p);
}
