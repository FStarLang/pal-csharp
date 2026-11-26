module DependentCall.CapabilityLocal
#lang-pulse
open Pulse
open DependentCall.Capability
module R = Pulse.Lib.Reference
module C = Pulse.Lib.CSharp.Capability
module E = Pulse.Lib.CSharp.Enumerable.Capability
module O = Pulse.Lib.CSharp.Enumerable.Observation

#set-options "--z3rlimit 10"

fn allocated (t r:Type0) (owner:R.ref t) (initial:view t r)
  (e:E.enumerable t)
  (#owner_state:erased t)
  (#state:erased (O.model t r)) (#p:perm)
  (#w:erased (C.descriptor (O.model t r) (O.slots t r)))
  preserves R.pts_to owner owner_state ** E.pts_to O.contents e w p state
  requires pure (initial.source == owner)
  returns result:bool
  ensures pure (result == C.supports w)
{
  let mut v = initial;
  consumer t r owner v #(O.model t r) #(O.slots t r)
    (O.contents #t #r) (O.scalar #t #r)
    (O.select_length #t #r) (O.select_scalar #t #r) e
    #owner_state #1.0R #(hide initial) #state #p #w
}
