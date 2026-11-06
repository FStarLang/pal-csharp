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

let region_cb (#a #v #r: Type0) (view: B.box a -> a -> v) (p: Seq.seq (v & r) -> slprop) =
  (#tr: erased (Seq.seq (v & r))) -> (#q: perm) -> (#h: erased (heap a)) ->
  (x: B.box a { not (B.is_null x) /\ mem h x }) ->
  stt r (p tr ** region #a #q h)
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
