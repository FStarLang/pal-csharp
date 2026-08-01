module Func_CounterClient_ValueIsNonNegative
#lang-pulse

open Pulse

module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module Seq = FStar.Seq

(* F17 / R3.9d: the client holds `class_Counter__inv var_c m` opaquely -- it never unfolds
   it -- and still concludes a fact about the model, because the fact travels in the *type*
   of `m`. Weaken `class_Counter__model__pred` to `True` and this fails with `Error 19`. *)
fn func_CounterClient_ValueIsNonNegative
     (var_c: Class_Counter.class_Counter)
     (#m: erased Class_Counter.class_Counter__model)
  preserves Class_Counter.class_Counter__inv var_c m
  ensures  pure ((Class_Counter.spec_Counter_Value m) >= 0)
{
  ()
}
