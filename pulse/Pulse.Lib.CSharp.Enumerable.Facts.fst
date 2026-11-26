module Pulse.Lib.CSharp.Enumerable.Facts
#lang-pulse
open Pulse
module C = Pulse.Lib.CSharp.Capability
module E = Pulse.Lib.CSharp.Enumerable.Capability
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

// A successful classification exposes only a checked logical observation.
// Missing APIs produce no fact; no cast success or failure is assumed.
fn matches (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (fact:m -> prop)
  (select:C.reader m unit api (fun m _ -> fact m)) (e:E.enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  preserves E.pts_to contents e w p model
  returns result:bool
  ensures pure (result == C.supports w /\ (result ==> fact model))
{
  let result = E.matches contents e;
  if result {
    E.read contents (fun m _ -> fact m) select e;
    true
  } else {
    false
  }
}
