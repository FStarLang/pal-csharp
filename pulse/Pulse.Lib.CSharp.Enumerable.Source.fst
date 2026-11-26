module Pulse.Lib.CSharp.Enumerable.Source
#lang-pulse

// A source-retaining enumerable loan. Unlike Enumerable.view, this loan owns
// BOTH the source and its checked snapshot. The source may be a coherent runtime
// descriptor; it need not represent a single exact CLR class.
//
// This is the ownership bridge, not a CLR cast implementation. An adapter must
// supply the descriptor, its ownership predicate and its model-to-items map.
// A base-class cast of a borrowing view must retain the view's resource and
// dispatch, not substitute the base class's invariant.
//
// `lend` requires a checked contents correspondence (for example established by
// verified Count/CopyTo). Opening and closing transfers the SAME source resource;
// no identity injectivity, failed-cast assumption, or resource duplication is used.
// Aliased arguments require permissions that can actually be separated.

open Pulse
open Pulse.Lib.CSharp.Casts
module A = Pulse.Lib.CSharp.Array.Base
module E = Pulse.Lib.CSharp.Enumerable
module R = Pulse.Lib.Reference
module I32 = FStar.Int32
module Seq = FStar.Seq
module CS = Pulse.Lib.CSharp.Seq

#set-options "--z3rlimit 10"

noeq type enumerable (t s: Type0) = { object: s; snapshot: E.enumerable t }

let source (#t #s: Type0) (e: enumerable t s) : s = e.object
let is_collection (#t #s: Type0) (e: enumerable t s) : bool =
  E.is_collection e.snapshot

let opened (#t #s #m: Type0) (contents: m -> Seq.seq t)
  ([@@@mkey] e: enumerable t s) (p: perm) (model: erased m) : slprop =
  E.pts_to e.snapshot #p (contents model)

let pts_to (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  ([@@@mkey] e: enumerable t s) (p: perm) (model: erased m) : slprop =
  owns (source e) p model ** opened contents e p model

let view (#t #s: Type0) (o: s) (a: A.array t) (coll: bool)
  : e: enumerable t s { source e == o /\ is_collection e == coll } =
  { object = o; snapshot = E.view a coll }

ghost
fn open_source (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s) (#p: perm) (#model: erased m)
  requires pts_to owns contents e p model
  ensures owns (source e) p model ** opened contents e p model
{
  unfold (pts_to owns contents e p model);
}

ghost
fn close_source (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s) (#p: perm) (#model: erased m)
  requires owns (source e) p model ** opened contents e p model
  ensures pts_to owns contents e p model
{
  fold (pts_to owns contents e p model);
}

// Forwarding to a snapshot-only callee temporarily hides the source resource.
// The callee receives the SAME snapshot, not a newly allocated/copied array.
// Keeping the source in a receipt prevents opening a concrete cast concurrently.
let snapshot_receipt (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  ([@@@mkey] e: enumerable t s) (p: perm) (model: erased m) : slprop =
  owns (source e) p model

ghost
fn forward_snapshot (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s) (#p: perm) (#model: erased m)
  requires pts_to owns contents e p model
  ensures snapshot_receipt owns contents e p model **
    E.pts_to e.snapshot #p (contents model)
{
  open_source owns contents e;
  unfold (opened contents e p model);
  fold (snapshot_receipt owns contents e p model);
}

ghost
fn restore_snapshot (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s) (#p: perm) (#model: erased m)
  requires snapshot_receipt owns contents e p model **
    E.pts_to e.snapshot #p (contents model)
  ensures pts_to owns contents e p model
{
  unfold (snapshot_receipt owns contents e p model);
  fold (opened contents e p model);
  close_source owns contents e;
}

ghost
fn lend (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (o: s) (a: A.array t) (coll: bool) (#p: perm) (#model: erased m)
  (#items: erased (Seq.seq t) { Seq.equal items (contents model) })
  requires owns o p model ** A.pts_to a #p items
  ensures pts_to owns contents (view o a coll) p model
{
  Seq.lemma_eq_elim (reveal items) (contents model);
  E.lend a coll;
  rewrite (E.pts_to (E.view a coll) #p items)
    as (E.pts_to (view o a coll).snapshot #p (contents model));
  fold (opened contents (view o a coll) p model);
  close_source owns contents (view o a coll);
}

ghost
fn unlend (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (o: s) (a: A.array t) (coll: bool) (#p: perm) (#model: erased m)
  requires pts_to owns contents (view o a coll) p model
  ensures owns o p model ** A.pts_to a #p (contents model)
{
  open_source owns contents (view o a coll);
  unfold (opened contents (view o a coll) p model);
  rewrite (E.pts_to (view o a coll).snapshot #p (contents model))
    as (E.pts_to (E.view a coll) #p (contents model));
  E.unlend a coll;
}

ghost
fn pts_to_len (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s) (#p: perm) (#model: erased m)
  preserves pts_to owns contents e p model
  ensures pure (Seq.length (contents model) < pow2 31)
{
  open_source owns contents e;
  unfold (opened contents e p model);
  E.pts_to_len e.snapshot;
  fold (opened contents e p model);
  close_source owns contents e;
}

fn count (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s { is_collection e }) (#p: perm) (#model: erased m)
  preserves pts_to owns contents e p model
  returns n: I32.t
  ensures pure (I32.v n == Seq.length (contents model))
{
  open_source owns contents e;
  unfold (opened contents e p model);
  let n = E.count e.snapshot;
  fold (opened contents e p model);
  close_source owns contents e;
  n
}

fn move_next (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s) (cursor: R.ref I32.t)
  (#p: perm) (#model: erased m) (#k: erased I32.t)
  preserves pts_to owns contents e p model
  requires R.pts_to cursor k
  returns b: bool
  ensures R.pts_to cursor (E.advance (contents model) k) **
    pure (b == (0 <= I32.v k /\ I32.v k < Seq.length (contents model)) /\
          Seq.length (contents model) < pow2 31)
{
  open_source owns contents e;
  unfold (opened contents e p model);
  let b = E.move_next e.snapshot cursor;
  fold (opened contents e p model);
  close_source owns contents e;
  b
}

fn current (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s) (cursor: R.ref I32.t)
  (#p: perm) (#model: erased m)
  (#k: erased (k: I32.t { 1 <= I32.v k /\ I32.v k <= Seq.length (contents model) }))
  preserves pts_to owns contents e p model ** R.pts_to cursor k
  returns x: t
  ensures rewrites_to x (Seq.index (contents model) (I32.v k - 1))
{
  open_source owns contents e;
  unfold (opened contents e p model);
  let x = E.current e.snapshot cursor;
  fold (opened contents e p model);
  close_source owns contents e;
  x
}

fn copy_to (#t #s #m: Type0)
  (owns: s -> perm -> m -> slprop) (contents: m -> Seq.seq t)
  (e: enumerable t s { is_collection e }) (dst: A.array t) (i: I32.t)
  (#p: perm) (#model: erased m)
  (#d: erased (Seq.seq t) {
    I32.v i >= 0 /\ I32.v i + Seq.length (contents model) <= Seq.length d })
  preserves pts_to owns contents e p model
  requires A.pts_to dst d
  ensures A.pts_to dst
    (CS.copied_at (contents model) 0 d (I32.v i) (Seq.length (contents model)))
{
  open_source owns contents e;
  unfold (opened contents e p model);
  E.copy_to e.snapshot dst i;
  fold (opened contents e p model);
  close_source owns contents e;
}
