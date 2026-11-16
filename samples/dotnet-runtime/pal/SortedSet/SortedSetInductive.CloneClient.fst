module SortedSetInductive.CloneClient
#lang-pulse

open Pulse.Lib.Pervasives
module C = SortedSetInductive.Clone
module S = SortedSetInductive.CloneStep
module O = SortedSetInductive.Ownership
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

let shape (#a: Type0) (source: O.tree a) (src: N.class_Node__opt a) (record: N.class_Node__raw a) =
  source == T.Branch (T.left source) (src, O.entry record) (T.right source) /\
  O.left record == O.top (T.left source) /\ O.right record == O.top (T.right source)

unfold let opened_job (#a: Type0) (source: O.tree a) (src target: N.class_Node a) (p: perm) =
  exists* (record: N.class_Node__raw a).
    O.raw src record p ** O.owns (T.left source) p ** O.owns (T.right source) p **
    O.fresh target (O.item record) (O.node_color record) ** pure (shape source src record)

ghost fn open_job (#a: Type0) (source: O.tree a) (src target: N.class_Node a) (p: perm)
  requires C.todo source target p ** pure (O.top source == src)
  ensures opened_job source src target p
{
  assert (pure (T.Branch? source));
  let l = T.left source;
  let r = T.right source;
  let e = T.Branch?._1 source;
  rewrite (C.todo source target p) as (C.todo (T.Branch l e r) target p);
  unfold (C.todo (T.Branch l e r) target p);
  rewrite (O.owns (T.Branch l e r) p) as (O.owns source p);
  S.open_source source src p;
  unfold (S.opened_source source src p);
  with record. _;
  rewrite (O.held target (fst (snd e)) (snd (snd e)) B.null B.null 1.0R) as
    (O.fresh target (O.item record) (O.node_color record));
  fold (opened_job source src target p);
}

ghost fn close_left (#a: Type0) (source: O.tree a) (src target: N.class_Node__opt a)
    (record copy: N.class_Node__raw a) (prefix pending: Seq.seq (C.pair a)) (p: perm)
  requires O.raw src record p ** O.raw target copy 1.0R **
    C.cloning (T.left source) (O.left copy)
      (S.jobs (O.top (T.left source)) (O.left copy)) (T.size (T.left source)) p **
    O.owns (T.right source) p **
    pure (shape source src record /\ O.entry copy == O.entry record /\ O.right copy == B.null /\
      pending == Seq.append prefix (S.jobs (O.top (T.left source)) (O.left copy)))
  ensures S.left_stage source target prefix pending p
{
  let l = T.left source;
  let r = T.right source;
  rewrite (C.cloning (T.left source) (O.left copy)
    (S.jobs (O.top (T.left source)) (O.left copy)) (T.size (T.left source)) p) as
    (C.cloning l (O.left copy) (S.jobs (O.top l) (O.left copy)) (T.size l) p);
  rewrite (O.owns (T.right source) p) as (O.owns r p);
  fold (S.left_stage (T.Branch l (src, O.entry record) r) target prefix pending p);
  rewrite (S.left_stage (T.Branch l (src, O.entry record) r) target prefix pending p) as
    (S.left_stage source target prefix pending p);
}

unfold let left_opened (#a: Type0) (source: O.tree a) (src target: N.class_Node__opt a)
    (prefix pending: Seq.seq (C.pair a)) (p: perm) =
  exists* (record copy: N.class_Node__raw a).
    O.raw src record p ** O.raw target copy 1.0R **
    C.cloning (T.left source) (O.left copy)
      (S.jobs (O.top (T.left source)) (O.left copy)) (T.size (T.left source)) p **
    O.owns (T.right source) p **
    pure (shape source src record /\ O.entry copy == O.entry record /\ O.right copy == B.null /\
      pending == Seq.append prefix (S.jobs (O.top (T.left source)) (O.left copy)))

ghost fn open_left (#a: Type0) (source: O.tree a) (src target: N.class_Node a)
    (prefix pending: Seq.seq (C.pair a)) (p: perm)
  requires S.left_stage source target prefix pending p ** pure (O.top source == src)
  ensures left_opened source src target prefix pending p
{
  assert (pure (T.Branch? source));
  let l = T.left source;
  let r = T.right source;
  let e = T.Branch?._1 source;
  rewrite (S.left_stage source target prefix pending p) as
    (S.left_stage (T.Branch l e r) target prefix pending p);
  unfold (S.left_stage (T.Branch l e r) target prefix pending p);
  with lt. _;
  rewrite (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p) as
    (O.held src (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p);
  rewrite (C.cloning l lt (S.jobs (O.top l) lt) (T.size l) p) as
    (C.cloning (T.left source) lt (S.jobs (O.top (T.left source)) lt) (T.size (T.left source)) p);
  rewrite (O.owns r p) as (O.owns (T.right source) p);
  fold (left_opened source src target prefix pending p);
}

ghost fn close_complete (#a: Type0) (source: O.tree a) (src target: N.class_Node__opt a)
    (record copy: N.class_Node__raw a) (prefix pending: Seq.seq (C.pair a)) (p: perm)
  requires O.raw src record p ** O.raw target copy 1.0R **
    C.cloning (T.left source) (O.left copy)
      (S.jobs (O.top (T.left source)) (O.left copy)) (T.size (T.left source)) p **
    C.cloning (T.right source) (O.right copy)
      (S.jobs (O.top (T.right source)) (O.right copy)) (T.size (T.right source)) p **
    pure (shape source src record /\ O.entry copy == O.entry record /\
      pending == Seq.append
        (Seq.append prefix (S.jobs (O.top (T.left source)) (O.left copy)))
        (S.jobs (O.top (T.right source)) (O.right copy)))
  ensures S.complete source target prefix pending p
{
  let l = T.left source;
  let r = T.right source;
  rewrite (C.cloning (T.left source) (O.left copy)
    (S.jobs (O.top (T.left source)) (O.left copy)) (T.size (T.left source)) p) as
    (C.cloning l (O.left copy) (S.jobs (O.top l) (O.left copy)) (T.size l) p);
  rewrite (C.cloning (T.right source) (O.right copy)
    (S.jobs (O.top (T.right source)) (O.right copy)) (T.size (T.right source)) p) as
    (C.cloning r (O.right copy) (S.jobs (O.top r) (O.right copy)) (T.size r) p);
  fold (S.complete (T.Branch l (src, O.entry record) r) target prefix pending p);
  rewrite (S.complete (T.Branch l (src, O.entry record) r) target prefix pending p) as
    (S.complete source target prefix pending p);
}
