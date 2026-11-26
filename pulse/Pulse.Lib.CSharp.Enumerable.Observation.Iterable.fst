module Pulse.Lib.CSharp.Enumerable.Observation.Iterable
#lang-pulse
open Pulse
module C = Pulse.Lib.CSharp.Capability
module I = Pulse.Lib.CSharp.Capability.Iterator
module O = Pulse.Lib.CSharp.Enumerable.Observation
module I32 = FStar.Int32

noeq type slots (t r:Type0) (fact:O.model t r -> prop) (i:Type0)
  (owns:i -> perm -> O.model t r -> slprop) = {
  observations:O.slots t r i owns;
  iteration:I.slots (O.model t r) t i owns O.contents;
  facts:x:i -> #p:perm -> #m:erased (O.model t r) ->
    stt unit (owns x p m) (fun _ -> owns x p m ** pure (fact m));
}

let make (#t #r:Type0) (#fact:O.model t r -> prop)
  (#i:Type0) (#owns:i -> perm -> O.model t r -> slprop)
  (observations:O.slots t r i owns)
  (iteration:I.slots (O.model t r) t i owns O.contents)
  (facts:(x:i -> #p:perm -> #m:erased (O.model t r) ->
    stt unit (owns x p m) (fun _ -> owns x p m ** pure (fact m))))
  : slots t r fact i owns =
  { observations; iteration; facts }

let select_length (#t #r:Type0) (#fact:O.model t r -> prop)
  : C.reader (O.model t r) I32.t (slots t r fact) O.length_post =
  fun i owns api -> O.select_length i owns api.observations

let select_scalar (#t #r:Type0) (#fact:O.model t r -> prop)
  : C.reader (O.model t r) r (slots t r fact) O.scalar_post =
  fun i owns api -> O.select_scalar i owns api.observations

let select_iterator (#t #r:Type0) (#fact:O.model t r -> prop)
  : I.selector (O.model t r) t (slots t r fact) O.contents =
  fun i owns api -> api.iteration

let select_facts (#t #r:Type0) (#fact:O.model t r -> prop)
  : C.reader (O.model t r) unit (slots t r fact) (fun m _ -> fact m) =
  fun i owns api -> api.facts
