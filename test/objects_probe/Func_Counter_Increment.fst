module Func_Counter_Increment
#lang-pulse

open Pulse

module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module Seq = FStar.Seq

fn func_Counter_Increment (var_this: Class_Counter.class_Counter) (#m: erased Class_Counter.class_Counter__model)
  requires Class_Counter.class_Counter__inv var_this m **
           pure ((Class_Counter.spec_Counter_Value m) < 2147483647)
  ensures  exists* m2. Class_Counter.class_Counter__inv var_this m2 **
           pure ((Class_Counter.spec_Counter_Value m2) ==
                 ((Class_Counter.spec_Counter_Value m) + 1))
{
  unfold Class_Counter.class_Counter__inv var_this m;
  let t0 = B.op_Bang var_this;
  B.op_Colon_Equals var_this
    ({ t0 with Class_Counter.fld_count = (I32.add t0.Class_Counter.fld_count 1l) });
  let t1 = B.op_Bang var_this;
  fold Class_Counter.class_Counter__inv var_this (I32.v t1.Class_Counter.fld_count);
}
