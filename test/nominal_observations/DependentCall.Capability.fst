module DependentCall.Capability
#lang-pulse
open Pulse
module R = Pulse.Lib.Reference
module C = Pulse.Lib.CSharp.Capability
module E = Pulse.Lib.CSharp.Enumerable.Capability
module O = Pulse.Lib.CSharp.Enumerable.Observation
module I32 = FStar.Int32
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

// No generated modules or nominal classes: only generic capability support.
noeq type view (t r:Type0) = {
  source:R.ref t;
  selected:r;
  cache:I32.t;
  item:t;
  order:r;
}

fn consumer (t r:Type0) (owner:R.ref t) (v:R.ref (view t r))
  (#m:Type0) (#api:(i:Type0) -> (i -> perm -> m -> slprop) -> Type0)
  (contents:m -> Seq.seq t) (scalar:m -> r)
  (lr:C.reader m I32.t api (fun m n -> I32.v n == Seq.length (contents m)))
  (sr:C.reader m r api (fun m n -> n == scalar m))
  (e:E.enumerable t)
  (#owner_state:erased t) (#owner_perm:perm) (#before:erased (view t r))
  (#state:erased m) (#p:perm) (#w:erased (C.descriptor m api))
  requires R.pts_to owner #owner_perm owner_state **
    R.pts_to v before ** E.pts_to contents e w p state **
    pure ((reveal before).source == owner)
  returns result:bool
  ensures exists* after.
    R.pts_to owner #owner_perm owner_state ** R.pts_to v after **
    E.pts_to contents e w p state **
    pure (after.source == owner /\ after == before /\
      after.selected == (reveal before).selected /\
      I32.v after.cache == I32.v (reveal before).cache /\
      after.item == (reveal before).item /\ after.order == (reveal before).order /\
      ((reveal before).source == owner ==> result == C.supports w))
{
  E.matches contents e
}

fn parameterized (t r:Type0) (owner:R.ref t) (v:R.ref (view t r))
  (#m:Type0) (#api:(i:Type0) -> (i -> perm -> m -> slprop) -> Type0)
  (contents:m -> Seq.seq t) (scalar:m -> r)
  (lr:C.reader m I32.t api (fun m n -> I32.v n == Seq.length (contents m)))
  (sr:C.reader m r api (fun m n -> n == scalar m))
  (e:E.enumerable t)
  (#owner_state:erased t) (#before:erased (view t r))
  (#state:erased m) (#p:perm) (#w:erased (C.descriptor m api))
  preserves R.pts_to owner owner_state ** R.pts_to v before **
    E.pts_to contents e w p state
  requires pure ((reveal before).source == owner)
  returns result:bool
  ensures pure (result == C.supports w)
{
  consumer t r owner v #m #api contents scalar lr sr e
    #owner_state #1.0R #before #state #p #w
}
