module SortedSetInductive.CloneStep
#lang-pulse

open Pulse.Lib.Pervasives
module C = SortedSetInductive.Clone
module O = SortedSetInductive.Ownership
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

let jobs (#a: Type0) (src target: N.class_Node__opt a) : Tot (Seq.seq (C.pair a)) =
  if B.is_null src || B.is_null target then Seq.empty
  else Seq.create 1 (src, target)

// Pointer-only C# specification operations carry their type argument explicitly.
let jobs_for (a: Type0) (src target: N.class_Node__opt a) = jobs src target

unfold let opened_source (#a: Type0) (source: O.tree a) (src: N.class_Node__opt a) (p: perm) =
  exists* (record: N.class_Node__raw a).
    O.raw src record p ** O.owns (T.left source) p ** O.owns (T.right source) p **
    pure (source == T.Branch (T.left source) (src, O.entry record) (T.right source) /\
      O.left record == O.top (T.left source) /\ O.right record == O.top (T.right source))

ghost fn open_source (#a: Type0) (source: O.tree a) (src: N.class_Node a) (p: perm)
  requires O.owns source p ** pure (O.top source == src)
  ensures opened_source source src p
{
  assert (pure (T.Branch? source));
  let l = T.left source;
  let r = T.right source;
  let e = T.Branch?._1 source;
  rewrite (O.owns source p) as (O.owns (T.Branch l e r) p);
  unfold (O.owns (T.Branch l e r) p);
  rewrite (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p) as
    (O.held src (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p);
  rewrite (O.owns l p) as (O.owns (T.left source) p);
  rewrite (O.owns r p) as (O.owns (T.right source) p);
  fold (opened_source source src p);
}

ghost fn seed_opened (#a: Type0) (source: O.tree a) (src target: N.class_Node a)
    (record: N.class_Node__raw a) (p: perm)
  requires O.raw src record p ** O.owns (T.left source) p ** O.owns (T.right source) p **
    O.fresh target (O.item record) (O.node_color record) **
    pure (source == T.Branch (T.left source) (src, O.entry record) (T.right source) /\
      O.left record == O.top (T.left source) /\ O.right record == O.top (T.right source))
  ensures C.cloning source target (jobs src target) (T.size source) p
{
  let l = T.left source;
  let r = T.right source;
  let key = O.item record;
  let red = O.red record;
  rewrite (O.owns (T.left source) p) as (O.owns l p);
  rewrite (O.owns (T.right source) p) as (O.owns r p);
  rewrite (O.raw src record p) as (O.held src key red (O.top l) (O.top r) p);
  fold (O.owns (T.Branch l (src, (key, red)) r) p);
  rewrite (O.fresh target (O.item record) (O.node_color record)) as
    (O.fresh target key (O.color red));
  C.seed l r src target key red p;
  rewrite (C.cloning (T.Branch l (src, (key, red)) r) target
    (Seq.create 1 (src, target)) (T.size (T.Branch l (src, (key, red)) r)) p) as
    (C.cloning source target (jobs src target) (T.size source) p);
}

ghost fn empty_source (#a: Type0) (source: O.tree a) (p: perm)
  requires O.owns source p ** pure (O.top source == B.null)
  ensures C.cloning source B.null Seq.empty (T.size source) p ** pure (T.Leaf? source)
{
  match source {
    T.Leaf -> {
      unfold (O.owns source p);
      C.empty #a p;
    }
    T.Branch l e r -> {
      unfold (O.owns source p);
      B.pts_to_not_null (fst e);
      assert (pure False);
    }
  }
}

// Between child visits, unvisited source ownership remains explicit.
let left_stage (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (prefix pending: Seq.seq (C.pair a)) (p: perm) =
  match source with
  | T.Leaf -> pure False
  | T.Branch l e r ->
    exists* (lt: N.class_Node__opt a).
      O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p **
      O.held target (fst (snd e)) (snd (snd e)) lt B.null 1.0R **
      C.cloning l lt (jobs (O.top l) lt) (T.size l) p ** O.owns r p **
      pure (pending == Seq.append prefix (jobs (O.top l) lt))

let complete (#a: Type0) (source: O.tree a) (target: N.class_Node__opt a)
    (prefix pending: Seq.seq (C.pair a)) (p: perm) =
  match source with
  | T.Leaf -> pure False
  | T.Branch l e r ->
    exists* (lt rt: N.class_Node__opt a).
      O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p **
      O.held target (fst (snd e)) (snd (snd e)) lt rt 1.0R **
      C.cloning l lt (jobs (O.top l) lt) (T.size l) p **
      C.cloning r rt (jobs (O.top r) rt) (T.size r) p **
      pure (pending == Seq.append (Seq.append prefix (jobs (O.top l) lt)) (jobs (O.top r) rt))
