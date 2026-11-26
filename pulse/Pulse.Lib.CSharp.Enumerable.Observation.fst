module Pulse.Lib.CSharp.Enumerable.Observation
#lang-pulse

open Pulse
module C = Pulse.Lib.CSharp.Capability
module E = Pulse.Lib.CSharp.Enumerable.Capability
module S = Pulse.Lib.CSharp.Enumerable.Source
module Seq = FStar.Seq
module I32 = FStar.Int32

#set-options "--z3rlimit 10"

// The bounded frontend schema: one length and one scalar observation.
// Names and implementations come from checked nominal getter annotations.
noeq type slots (t r i:Type0) (owns:i -> perm -> model t r -> slprop) : Type u#4 = {
  length: (x:i -> #p:perm -> #m:erased (model t r) ->
    stt I32.t (owns x p m)
      (fun result -> owns x p m ** pure (I32.v result == Seq.length (reveal m).items)));
  observation: (x:i -> #p:perm -> #m:erased (model t r) ->
    stt r (owns x p m)
      (fun result -> owns x p m ** pure (result == (reveal m).scalar)));
}
let make #t #r #i #owns length observation : slots t r i owns = { length; observation }
let select_length (#t #r:Type0) (i:Type0) (owns:i -> perm -> model t r -> slprop)
  (s:slots t r i owns) = s.length
let select_scalar (#t #r:Type0) (i:Type0) (owns:i -> perm -> model t r -> slprop)
  (s:slots t r i owns) = s.observation

