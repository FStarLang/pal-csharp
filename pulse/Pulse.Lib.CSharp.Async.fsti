module Pulse.Lib.CSharp.Async
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Send

(* Trusted CLR task boundary, following Async.async_joinable. A task's value is
   duplicable, but its completion permission is not. Faulted/cancelled tasks do
   not return through await in this partial-correctness, normal-completion model.
   No termination, scheduler fairness, or exception recovery is assumed. *)
val task (a:Type0) (post:a -> slprop) : Type0
val pending (#a:Type0) (#post:a -> slprop) (t:task a post) : slprop

val start (#a:Type0) (#pre:slprop) (#post:a -> slprop)
  {| is_send pre, ((x:a) -> is_send (post x)) |}
  (f:unit -> stt_div a pre post)
  : stt (task a post) pre (fun t -> pending t)

instance val send_pending #a #post (t:task a post) : is_send (pending t)

divergent
fn await (#a:Type0) (#post:a -> slprop)
  (t:task a post)
  requires pending t
  returns x:a
  ensures post x

val completed (#a:Type0) (x:a)
  : stt (task a (fun r -> pure (r == x))) emp (fun t -> pending t)

val delay (milliseconds:FStar.Int32.t{FStar.Int32.v milliseconds >= 0})
  : stt (task unit (fun _ -> emp)) emp (fun t -> pending t)
