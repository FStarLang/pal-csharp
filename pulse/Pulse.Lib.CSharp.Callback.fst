module Pulse.Lib.CSharp.Callback
#lang-pulse

/// R27.39. A callback over the pointers of a region: the type of a `[Callback]` delegate
/// parameter. The callee states nothing about what the callback does, only the protocol it
/// follows: each call is recorded in a trace of (view of the node, result) pairs, and the
/// caller's predicate `p` over that trace is what the callback keeps. The callee holds the
/// region at any fraction and hands it to the callback; the callback hands it back unchanged.

open Pulse
open Pulse.Lib.CSharp.Region
module B = Pulse.Lib.Box
module Seq = FStar.Seq

/// How many times a callback may be called: fewer than an `int` counts. The callee proves
/// it before each call (a walk calls it at most once per node of a region an `int` counts),
/// and the callback may assume it, which is what lets it count its calls in an `int`.
unfold let max_calls : int = 2147483647

unfold let callable (#e: Type0) (tr: Seq.seq e) : bool = Seq.length tr < max_calls

/// R32.11. The callee may also promise a bound `n` of its own on the calls (a walk calls back
/// at most once per node, so fewer times than the tree has nodes), which the callback may
/// assume. A callee that promises none passes `max_bound`.
unfold let max_bound : erased int = hide max_calls

let region_cb (#a #v #r: Type0) (view: B.box a -> a -> v) (p: Seq.seq (v & r) -> slprop)
    (n: erased int) =
  (#tr: erased (Seq.seq (v & r))) -> (#q: perm) -> (#h: erased (heap a)) ->
  (x: B.box a { not (B.is_null x) /\ mem h x }) ->
  stt r (p tr ** region #a #q h ** pure (Seq.length tr < max_calls /\ Seq.length tr < reveal n))
        (fun res -> p (Seq.snoc tr (view x (get h x), res)) ** region #a #q h)

/// The view of `x` in `h`, as the trace records it.
let view_at (#a #v: Type0) (view: B.box a -> a -> v) (h: heap a) (x: B.box a { mem h x }) : v =
  view x (get h x)

/// The trace the protocol is at now. It does nothing; its `rewrites_to` is what lets a
/// loop's `decreases` name the trace, as `Region.current` names a heap.
ghost fn trace_now (#e: Type0) (p: Seq.seq e -> slprop) (#tr: erased (Seq.seq e)) (_: unit)
  preserves p tr
  returns  r: Seq.seq e
  ensures  rewrites_to r (reveal tr)
{
  reveal tr
}

/// R27.43. The model an object's invariant is at now, for a loop's `decreases`, as
/// `trace_now` names a trace.
ghost fn model_now (#m: Type0) (inv: m -> slprop) (#v: erased m) (_: unit)
  preserves inv v
  returns  r: m
  ensures  rewrites_to r (reveal v)
{
  reveal v
}
