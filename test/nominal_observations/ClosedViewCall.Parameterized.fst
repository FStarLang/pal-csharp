module ClosedViewCall.Parameterized
#lang-pulse
open Pulse
module R = Pulse.Lib.Reference
module C = Pulse.Lib.CSharp.Capability
module E = Pulse.Lib.CSharp.Enumerable.Capability
module O = Pulse.Lib.CSharp.Enumerable.Observation
open Func_Empty_at_Packet_CompareObserved

#set-options "--z3rlimit 10"

fn parameterized (t:Type0) (owner:Class_Packet.class_Packet t)
  (v:R.ref (Struct_Packet_Empty.struct_Packet_Empty t)) (e:E.enumerable t)
  (#owner_model:erased (Class_Packet.class_Packet__model t))
  (#before:erased (Struct_Packet_Empty.struct_Packet_Empty t))
  (#w:erased (C.descriptor (O.model t (Pulse.Lib.CSharp.Order.comparer t))
    (O.slots t (Pulse.Lib.CSharp.Order.comparer t))))
  (#p:perm) (#model:erased (O.model t (Pulse.Lib.CSharp.Order.comparer t)))
  preserves Class_Packet.class_Packet__inv owner owner_model **
    R.pts_to v before ** E.pts_to O.contents e w p model
  requires pure ((reveal before).Struct_Packet_Empty.fld_source == owner)
  returns result:bool
  ensures pure (result == C.supports w)
{
  func_Empty_at_Packet_CompareObserved t owner v
    #(O.model t (Pulse.Lib.CSharp.Order.comparer t))
    #(O.slots t (Pulse.Lib.CSharp.Order.comparer t))
    O.contents O.scalar O.select_length O.select_scalar e
    #owner_model #1.0R #before #model #p #w
}
