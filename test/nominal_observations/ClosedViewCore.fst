module ClosedViewCore
#lang-pulse
open Pulse
module R = Pulse.Lib.Reference
module C = Pulse.Lib.CSharp.Capability
module E = Pulse.Lib.CSharp.Enumerable.Capability
module O = Pulse.Lib.CSharp.Enumerable.Observation
module Seq = FStar.Seq

fn consumer (#t #m:Type0)
  (#api:(i:Type0) -> (i -> perm -> m -> slprop) -> Type0)
  (owner:Class_Packet.class_Packet t)
  (v:R.ref (Struct_Packet_Empty.struct_Packet_Empty t))
  (contents:m -> Seq.seq t) (scalar:m -> Pulse.Lib.CSharp.Order.comparer t)
  (lr:C.reader m FStar.Int32.t api (fun m n -> FStar.Int32.v n == Seq.length (contents m)))
  (sr:C.reader m (Pulse.Lib.CSharp.Order.comparer t) api (fun m n -> n == scalar m))
  (e:E.enumerable t)
  (#owner_model:erased (Class_Packet.class_Packet__model t)) (#owner_perm:perm)
  (#before:erased (Struct_Packet_Empty.struct_Packet_Empty t))
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  preserves Class_Packet.class_Packet__inv owner #owner_perm owner_model
  requires R.pts_to v before ** E.pts_to contents e w p model
  returns result:bool
  ensures exists* after. R.pts_to v after ** E.pts_to contents e w p model **
    pure (after == before /\ result == C.supports w)
{
  E.matches contents e
}

fn caller (t:Type0) (owner:Class_Packet.class_Packet t)
  (v:R.ref (Struct_Packet_Empty.struct_Packet_Empty t)) (e:E.enumerable t)
  (#owner_model:erased (Class_Packet.class_Packet__model t))
  (#before:erased (Struct_Packet_Empty.struct_Packet_Empty t))
  (#w:erased (C.descriptor (O.model t (Pulse.Lib.CSharp.Order.comparer t))
    (O.slots t (Pulse.Lib.CSharp.Order.comparer t))))
  (#p:perm) (#model:erased (O.model t (Pulse.Lib.CSharp.Order.comparer t)))
  preserves Class_Packet.class_Packet__inv owner owner_model
  preserves R.pts_to v before ** E.pts_to O.contents e w p model
  returns result:bool
  ensures pure (result == C.supports w)
{
  consumer owner v O.contents O.scalar O.select_length O.select_scalar e
}

