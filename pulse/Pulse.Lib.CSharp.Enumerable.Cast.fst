module Pulse.Lib.CSharp.Enumerable.Cast
#lang-pulse

open Pulse
module S = Pulse.Lib.CSharp.Enumerable.Source
module A = Pulse.Lib.CSharp.Array.Base
module D = FStar.Dyn
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

// The complete model is retained, not reconstructed from its projection.
// In particular two models with the same enumeration need not be equal.
noeq type descriptor (a m: Type0) =
  | Matches : value:a -> model:erased m -> descriptor a m
  | Misses : object:D.dyn -> descriptor a m

let resource (#a #m #t: Type0)
  (owns: a -> perm -> m -> slprop) (project: m -> Seq.seq t)
  (misses: D.dyn -> perm -> Seq.seq t -> slprop)
  (w: descriptor a m) (p: perm) (items: Seq.seq t) : slprop =
  match w with
  | Matches x model -> owns x p (reveal model) **
      pure (Seq.equal (project (reveal model)) items)
  | Misses o -> misses o p items

let contents (#t: Type0) (items: Seq.seq t) : Seq.seq t = items
let enumerable (a m t: Type0) = S.enumerable t (descriptor a m)
let matches (#a #m #t: Type0) (e: enumerable a m t) : bool =
  Matches? (S.source e)
let value (#a #m #t: Type0) (e: enumerable a m t { matches e }) : a =
  Matches?.value (S.source e)
let model (#a #m #t: Type0) (e: enumerable a m t { matches e }) : erased m =
  Matches?.model (S.source e)

let matching (#a #m #t: Type0) (o: a) (saved: erased m) (arr: A.array t) (coll: bool) =
  S.view (Matches o saved) arr coll
let nonmatching (#a #m #t: Type0) (o: D.dyn) (arr: A.array t) (coll: bool) =
  S.view (Misses #a #m o) arr coll

ghost
fn lend_match (#a #m #t: Type0)
  (owns: a -> perm -> m -> slprop) (project: m -> Seq.seq t)
  (misses: D.dyn -> perm -> Seq.seq t -> slprop)
  (o: a) (saved: erased m) (arr: A.array t) (coll: bool)
  (#p: perm) (#items: erased (Seq.seq t) { Seq.equal (project (reveal saved)) (reveal items) })
  requires owns o p (reveal saved) ** A.pts_to arr #p (reveal items)
  ensures S.pts_to (resource owns project misses) contents (matching o saved arr coll) p items
{
  fold (resource owns project misses (Matches o saved) p (reveal items));
  S.lend (resource owns project misses) contents (Matches o saved) arr coll;
}

ghost
fn unlend_match (#a #m #t: Type0)
  (owns: a -> perm -> m -> slprop) (project: m -> Seq.seq t)
  (misses: D.dyn -> perm -> Seq.seq t -> slprop)
  (o: a) (saved: erased m) (arr: A.array t) (coll: bool)
  (#p: perm) (#items: erased (Seq.seq t))
  requires S.pts_to (resource owns project misses) contents (matching o saved arr coll) p items
  ensures owns o p (reveal saved) ** A.pts_to arr #p (reveal items) **
    pure (Seq.equal (project (reveal saved)) (reveal items))
{
  S.unlend (resource owns project misses) contents (Matches o saved) arr coll;
  unfold (resource owns project misses (Matches o saved) p (reveal items));
}

ghost
fn lend_miss (#a #m #t: Type0)
  (owns: a -> perm -> m -> slprop) (project: m -> Seq.seq t)
  (misses: D.dyn -> perm -> Seq.seq t -> slprop)
  (o: D.dyn) (arr: A.array t) (coll: bool) (#p: perm) (#items: erased (Seq.seq t))
  requires misses o p (reveal items) ** A.pts_to arr #p (reveal items)
  ensures S.pts_to (resource owns project misses) contents (nonmatching o arr coll) p items
{
  fold (resource owns project misses (Misses o) p (reveal items));
  S.lend (resource owns project misses) contents (Misses o) arr coll;
}

ghost
fn unlend_miss (#a #m #t: Type0)
  (owns: a -> perm -> m -> slprop) (project: m -> Seq.seq t)
  (misses: D.dyn -> perm -> Seq.seq t -> slprop)
  (o: D.dyn) (arr: A.array t) (coll: bool) (#p: perm) (#items: erased (Seq.seq t))
  requires S.pts_to (resource owns project misses) contents (nonmatching o arr coll) p items
  ensures misses o p (reveal items) ** A.pts_to arr #p (reveal items)
{
  S.unlend (resource owns project misses) contents (Misses o) arr coll;
  unfold (resource owns project misses (Misses o) p (reveal items));
}

fn open_match (#a #m #t: Type0)
  (owns: a -> perm -> m -> slprop) (project: m -> Seq.seq t)
  (misses: D.dyn -> perm -> Seq.seq t -> slprop)
  (e: enumerable a m t { matches e }) (#p: perm) (#items: erased (Seq.seq t))
  requires S.pts_to (resource owns project misses) contents e p items
  returns x: a
  ensures owns x p (reveal (model e)) ** S.opened contents e p items **
    pure (x == value e /\ Seq.equal (project (reveal (model e))) (reveal items))
{
  S.open_source (resource owns project misses) contents e;
  let x = value e;
  rewrite (resource owns project misses (S.source e) p (reveal items))
    as (resource owns project misses (Matches x (model e)) p (reveal items));
  unfold (resource owns project misses (Matches x (model e)) p (reveal items));
  x
}

ghost
fn close_match (#a #m #t: Type0)
  (owns: a -> perm -> m -> slprop) (project: m -> Seq.seq t)
  (misses: D.dyn -> perm -> Seq.seq t -> slprop)
  (e: enumerable a m t { matches e }) (x: a { x == value e })
  (#p: perm) (#items: erased (Seq.seq t) {
    Seq.equal (project (reveal (model e))) (reveal items) })
  requires owns x p (reveal (model e)) ** S.opened contents e p items
  ensures S.pts_to (resource owns project misses) contents e p items
{
  fold (resource owns project misses (Matches x (model e)) p (reveal items));
  rewrite (resource owns project misses (Matches x (model e)) p (reveal items))
    as (resource owns project misses (S.source e) p (reveal items));
  S.close_source (resource owns project misses) contents e;
}
