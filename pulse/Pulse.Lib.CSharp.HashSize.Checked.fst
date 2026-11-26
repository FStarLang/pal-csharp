module Pulse.Lib.CSharp.HashSize.Checked
#lang-pulse

open Pulse.Lib.Pervasives
module I32 = FStar.Int32
module H = Pulse.Lib.CSharp.HashSize
module E = Pulse.Lib.CSharp.Exn

fn get_prime (min: I32.t)
  requires emp
  returns r: I32.t
  ensures pure (I32.v min >= 0 /\ H.size_ok (I32.v min) (I32.v r) /\ H.is_prime r)
  raises (fun e -> pure (I32.v min < 0 /\ e == E.BclException "System.ArgumentException"))
{
  if I32.lt min 0l {
    raise (E.BclException "System.ArgumentException")
  } else {
    let r = H.get_prime min;
    r
  }
}
