module Func_Counter_Get
#lang-pulse

open Pulse

module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module Seq = FStar.Seq

(* R4.11: the method assigns no field, so the contract collapses to `preserves`. *)
fn func_Counter_Get (var_this: Class_Counter.class_Counter) (#m: erased Class_Counter.class_Counter__model)
  preserves Class_Counter.class_Counter__inv var_this m
  returns  var_result: I32.t
  ensures  pure ((I32.v var_result) == (Class_Counter.spec_Counter_Value m))
{
  unfold Class_Counter.class_Counter__inv var_this m;
  let t0 = B.op_Bang var_this;
  fold Class_Counter.class_Counter__inv var_this m;
  t0.Class_Counter.fld_count
}
