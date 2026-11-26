module Pulse.Lib.CSharp.Capability
#lang-pulse

open Pulse
module D = FStar.Dyn
module A = Pulse.Lib.CSharp.Assumptions

#set-options "--z3rlimit 10"

// Resource-producing APIs carry predicates as well as executable slots.
// Their fixed kind includes both observation-only and iterator APIs.
let api_kind (m:Type0) = (i:Type0) -> (i -> perm -> m -> slprop) -> Type u#4

// A target-relative nominal base capability. The compiler, not this library,
// decides nominal assignability and installs the actual implementation's slots.
// A missing slot is not evidence that all other implementations miss the target.
// In particular an adapter for an unknown subclass cannot reuse a static base
// interface implementation merely because the subclass is assignable to it.
//
// `owns` belongs to the actual implementation. A borrowing view can keep its
// source tree, an exclusive view-state cell and its own logical projection here.
// Neither a successful cast nor dispatch exposes an ordinary base invariant.
noeq type descriptor (m: Type0)
  (api: api_kind m) = {
  impl: Type0;
  owns: impl -> perm -> m -> slprop;
  value: impl;
  base: option (api impl owns);
}

let supports (#m: Type0) (#api: api_kind m)
  (w: descriptor m api) : bool = Some? w.base

let make (#m:Type0) (#api:api_kind m)
  (i:Type0) (owns:i -> perm -> m -> slprop) (value:i) (base:option (api i owns))
  : w:descriptor m api { supports w == Some? base } =
  { impl = i; owns; value; base }

let source_at (#m: Type0) (#api: api_kind m)
  (o: D.dyn) (w: erased (descriptor m api)) (p: perm) (model: erased m) : slprop =
  pure (o == D.mkdyn (reveal w)) ** (reveal w).owns (reveal w).value p model

let base_at (#m: Type0) (#api: api_kind m)
  (o: D.dyn) (w: erased (descriptor m api)) (p: perm) (model: erased m) : slprop =
  source_at o w p model ** pure (supports w)

ghost
fn pack (#m:Type0) (#api:api_kind m)
  (i:Type0) (owns:i -> perm -> m -> slprop) (value:i) (base:option (api i owns))
  (#p:perm) (#model:erased m)
  requires owns value p model
  ensures source_at #m #api (D.mkdyn #(descriptor m api) (make #m #api i owns value base)) (hide (make #m #api i owns value base)) p model
{
  rewrite (owns value p model) as ((make #m #api i owns value base).owns (make #m #api i owns value base).value p model);
  fold (source_at (D.mkdyn #(descriptor m api) (make i owns value base)) (hide (make i owns value base)) p model);
}

ghost
fn unpack (#m:Type0) (#api:api_kind m)
  (i:Type0) (owns:i -> perm -> m -> slprop) (value:i) (base:option (api i owns))
  (#p:perm) (#model:erased m)
  requires source_at #m #api (D.mkdyn #(descriptor m api) (make #m #api i owns value base)) (hide (make #m #api i owns value base)) p model
  ensures owns value p model
{
  unfold (source_at (D.mkdyn #(descriptor m api) (make i owns value base)) (hide (make i owns value base)) p model);
  rewrite ((make #m #api i owns value base).owns (make #m #api i owns value base).value p model) as (owns value p model);
}

fn cast (#m: Type0) (#api: api_kind m)
  (o: D.dyn) (#w: erased (descriptor m api)) (#p: perm) (#model: erased m)
  preserves source_at o w p model
  returns result: option D.dyn
  ensures pure (result == (if supports w then Some o else None))
{
  unfold (source_at o w p model);
  let actual = A.recover #(descriptor m api) #w o;
  let result = if supports actual { Some o } else { None #D.dyn };
  fold (source_at o w p model);
  result
}

ghost
fn open_base (#m: Type0) (#api: api_kind m)
  (o: D.dyn) (#w: erased (descriptor m api) { supports w }) (#p: perm) (#model: erased m)
  requires source_at o w p model
  ensures base_at o w p model
{
  fold (base_at o w p model);
}

ghost
fn close_base (#m: Type0) (#api: api_kind m)
  (o: D.dyn) (#w: erased (descriptor m api)) (#p: perm) (#model: erased m)
  requires base_at o w p model
  ensures source_at o w p model
{
  unfold (base_at o w p model);
}

// A checked slot selector. It can select a scalar observation, a virtual method,
// or an iterator factory whose result owns its own protocol state. This first
// combinator is for resource-preserving observations; resource-producing
// factories use the same descriptor but need an explicitly indexed postresource.
let reader (m r:Type0) (api:api_kind m)
  (post:m -> r -> prop) =
  i:Type0 -> owns:(i -> perm -> m -> slprop) -> api i owns ->
    x:i -> #p:perm -> #model:erased m ->
      stt r (owns x p model) (fun result -> owns x p model ** pure (post model result))

fn read (#m #r: Type0) (#api: api_kind m)
  (post: m -> r -> prop)
  (select: reader m r api post)
  (o: D.dyn) (#w: erased (descriptor m api)) (#p: perm) (#model: erased m)
  preserves base_at o w p model
  returns result: r
  ensures pure (post model result)
{
  unfold (base_at o w p model);
  unfold (source_at o w p model);
  let actual = A.recover #(descriptor m api) #w o;
  rewrite ((reveal w).owns (reveal w).value p model) as
    (actual.owns actual.value p model);
  match actual.base {
    None -> { unreachable (); }
    Some slots -> {
      let operation = select actual.impl actual.owns slots;
      let result = operation actual.value #p #model;
      rewrite (actual.owns actual.value p model) as
        ((reveal w).owns (reveal w).value p model);
      fold (source_at o w p model);
      fold (base_at o w p model);
      result
    }
  }
}
