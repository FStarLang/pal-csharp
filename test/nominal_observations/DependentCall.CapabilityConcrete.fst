module DependentCall.CapabilityConcrete
#lang-pulse
open Pulse
open DependentCall.Capability
module R = Pulse.Lib.Reference
module C = Pulse.Lib.CSharp.Capability
module E = Pulse.Lib.CSharp.Enumerable.Capability
module O = Pulse.Lib.CSharp.Enumerable.Observation

#set-options "--z3rlimit 10"

fn parameterized (t r:Type0) (owner:R.ref t) (v:R.ref (view t r))
  (e:E.enumerable t)
  (#owner_state:erased t) (#before:erased (view t r))
  (#state:erased (O.model t r)) (#p:perm)
  (#w:erased (C.descriptor (O.model t r) (O.slots t r)))
  preserves R.pts_to owner owner_state ** R.pts_to v before **
    E.pts_to O.contents e w p state
  requires pure ((reveal before).source == owner)
  returns result:bool
  ensures pure (result == C.supports w)
{
  consumer t r owner v #(O.model t r) #(O.slots t r)
    (O.contents #t #r) (O.scalar #t #r)
    (O.select_length #t #r) (O.select_scalar #t #r) e
    #owner_state #1.0R #before #state #p #w
}
