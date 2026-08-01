module Func_Counter__ctor
#lang-pulse

open Pulse

module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module Seq = FStar.Seq

(* R4.12: allocate, establish the invariant, return the object.  Nothing is freed:
   Pulse slprops are affine and the CLR is garbage collected (F15). *)
fn func_Counter__ctor ()
  requires emp
  returns  var_result: Class_Counter.class_Counter
  ensures  exists* m. Class_Counter.class_Counter__inv var_result m **
           pure ((Class_Counter.spec_Counter_Value m) == 0)
{
  let var_result = B.alloc ({ Class_Counter.fld_count = 0l });
  fold Class_Counter.class_Counter__inv var_result 0;
  var_result
}
