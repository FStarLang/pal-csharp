module Pulse.Lib.CSharp.Enumerable.Observation
#lang-pulse
open Pulse
module C = Pulse.Lib.CSharp.Capability
module Seq = FStar.Seq
module I32 = FStar.Int32

noeq type model (t r:Type0) = { items:Seq.seq t; scalar:r }
val slots (t r i:Type0) (owns:i -> perm -> model t r -> slprop) : Type u#4
let contents (#t #r:Type0) (m:model t r) = m.items
let scalar (#t #r:Type0) (m:model t r) = m.scalar
let length_post (#t #r:Type0) (m:model t r) (v:I32.t) = I32.v v == Seq.length m.items
let scalar_post (#t #r:Type0) (m:model t r) (v:r) = v == m.scalar

val make (#t #r #i:Type0) (#owns:i -> perm -> model t r -> slprop)
  (length:(x:i -> #p:perm -> #m:erased (model t r) ->
    stt I32.t (owns x p m)
      (fun result -> owns x p m ** pure (length_post m result))))
  (observation:(x:i -> #p:perm -> #m:erased (model t r) ->
    stt r (owns x p m)
      (fun result -> owns x p m ** pure (scalar_post m result))))
  : slots t r i owns

val select_length (#t #r:Type0) : C.reader (model t r) I32.t (slots t r) length_post
val select_scalar (#t #r:Type0) : C.reader (model t r) r (slots t r) scalar_post

