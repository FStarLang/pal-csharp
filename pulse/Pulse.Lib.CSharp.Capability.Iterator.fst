module Pulse.Lib.CSharp.Capability.Iterator
#lang-pulse
open Pulse
module C = Pulse.Lib.CSharp.Capability
module D = FStar.Dyn
module A = Pulse.Lib.CSharp.Assumptions
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

noeq type state (t:Type0) = {
  pending:Seq.seq t;
  current:s:Seq.seq t { Seq.length s <= 1 };
}
let initial (#t:Type0) (items:Seq.seq t) : state t =
  { pending = items; current = Seq.empty }
let valid (#t:Type0) (s:state t) : bool = Seq.length s.current = 1
let ready (#t:Type0) (_:state t) : bool = true
let remaining (#t:Type0) (s:state t) = s.pending
let current_items (#t:Type0) (s:state t) = s.current
let moves (#t:Type0) (s:state t) : bool = Seq.length s.pending > 0
let step (#t:Type0) (s:state t) : state t =
  if moves s then
    { pending = Seq.slice s.pending 1 (Seq.length s.pending);
      current = Seq.slice s.pending 0 1 }
  else { pending = s.pending; current = Seq.empty }

// Convert the checked, pointwise EnumerationState transition laws into the
// abstract cursor state. Keeping sequence reasoning here avoids unfolding a
// concrete iterator's representation throughout the generated spatial fold.
let next_from_observations (#t:Type0) (s:state t)
  (before after current:Seq.seq t) (moved:bool)
  : Lemma
    (requires
      Seq.equal before s.pending /\
      moved == (Seq.length before > 0) /\
      Seq.length after == Seq.length before - (if moved then 1 else 0) /\
      (forall (i:nat). i < Seq.length after ==>
        Seq.index after i == Seq.index before (i + (if moved then 1 else 0))) /\
      Seq.length current == (if moved then 1 else 0) /\
      (moved ==> Seq.index current 0 == Seq.index before 0))
    (ensures Seq.equal after (step s).pending /\
      Seq.equal current (step s).current /\ moved == moves s)
  = if moved then () else ()

// Handles conceal the actual mutable iterator representation, not the source
// identity. Each installed resource predicate and operation is checked against
// the concrete implementation. No cast recovers an ordinary base invariant.
noeq type slots (m t i:Type0) (owns:i -> perm -> m -> slprop)
  (contents:m -> Seq.seq t) = {
  cursor_owns:i -> D.dyn -> perm -> m -> state t -> slprop;
  start:x:i -> #p:perm -> #model:erased m ->
    stt D.dyn (owns x p model)
      (fun h -> cursor_owns x h p model (initial (contents model)));
  next:x:i -> h:D.dyn -> #p:perm -> #model:erased m -> #s:erased (state t) ->
    stt bool (cursor_owns x h p model s)
      (fun result -> cursor_owns x h p model (step s) ** pure (result == moves s));
  value:x:i -> h:D.dyn -> #p:perm -> #model:erased m ->
    #s:erased (state t) { valid s } ->
    stt t (cursor_owns x h p model s)
      (fun result -> cursor_owns x h p model s ** pure (result == Seq.index (reveal s).current 0));
  dispose:x:i -> h:D.dyn -> #p:perm -> #model:erased m -> #s:erased (state t) ->
    stt unit (cursor_owns x h p model s) (fun _ -> cursor_owns x h p model s);
  // Scope release is NOT Dispose. It reclaims only nonescaping implementation
  // storage and returns the exact source resource, including partial traversal.
  release:x:i -> h:D.dyn -> #p:perm -> #model:erased m -> #s:erased (state t) ->
    stt unit (cursor_owns x h p model s) (fun _ -> owns x p model);
}

let selector (m t:Type0)
  (api:C.api_kind m)
  (contents:m -> Seq.seq t) =
  i:Type0 -> owns:(i -> perm -> m -> slprop) -> api i owns -> slots m t i owns contents

let operations (#m #t:Type0) (#api:C.api_kind m)
  (#contents:m -> Seq.seq t) (select:selector m t api contents)
  (w:C.descriptor m api { C.supports w }) : slots m t w.impl w.owns contents =
  match w.base with
  | None -> FStar.Pervasives.false_elim ()
  | Some api -> select w.impl w.owns api

let resource (#m #t:Type0) (#api:C.api_kind m)
  (#contents:m -> Seq.seq t) (select:selector m t api contents)
  (w:C.descriptor m api { C.supports w }) (h:D.dyn) (p:perm)
  (model:erased m) (s:erased (state t)) : slprop =
  (operations select w).cursor_owns w.value h p model s

let at (#m #t:Type0) (#api:C.api_kind m)
  (#contents:m -> Seq.seq t) (select:selector m t api contents)
  (o h:D.dyn) (w:erased (C.descriptor m api) { C.supports w }) (p:perm)
  (model:erased m) (s:erased (state t)) : slprop =
  pure (o == D.mkdyn (reveal w)) ** resource select (reveal w) h p model s

fn start (#m #t:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:selector m t api contents)
  (o:D.dyn) (#w:erased (C.descriptor m api) { C.supports w }) (#p:perm) (#model:erased m)
  requires C.base_at o w p model
  returns h:D.dyn
  ensures at select o h w p model (hide (initial (contents model)))
{
  unfold (C.base_at o w p model);
  unfold (C.source_at o w p model);
  let actual = A.recover #(C.descriptor m api) #w o;
  rewrite ((reveal w).owns (reveal w).value p model) as (actual.owns actual.value p model);
  let ops = operations select actual;
  let h = ops.start actual.value #p #model;
  rewrite each ops as (operations select actual);
  fold (resource select actual h p model (hide (initial (contents model))));
  rewrite (resource select actual h p model (hide (initial (contents model)))) as
    (resource select (reveal w) h p model (hide (initial (contents model))));
  fold (at select o h w p model (hide (initial (contents model))));
  h
}

fn next (#m #t:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:selector m t api contents)
  (o h:D.dyn) (#w:erased (C.descriptor m api) { C.supports w }) (#p:perm) (#model:erased m)
  (#s:erased (state t))
  requires at select o h w p model s
  returns result:bool
  ensures at select o h w p model (hide (step s)) ** pure (result == moves s)
{
  unfold (at select o h w p model s);
  let actual = A.recover #(C.descriptor m api) #w o;
  rewrite (resource select (reveal w) h p model s) as (resource select actual h p model s);
  unfold (resource select actual h p model s);
  let ops = operations select actual;
  rewrite each (operations select actual) as ops;
  let result = ops.next actual.value h #p #model #s;
  rewrite each ops as (operations select actual);
  fold (resource select actual h p model (hide (step s)));
  rewrite (resource select actual h p model (hide (step s))) as
    (resource select (reveal w) h p model (hide (step s)));
  fold (at select o h w p model (hide (step s)));
  result
}

fn value (#m #t:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:selector m t api contents)
  (o h:D.dyn) (#w:erased (C.descriptor m api) { C.supports w }) (#p:perm) (#model:erased m)
  (#s:erased (state t) { valid s })
  preserves at select o h w p model s
  returns result:t
  ensures pure (result == Seq.index (reveal s).current 0)
{
  unfold (at select o h w p model s);
  let actual = A.recover #(C.descriptor m api) #w o;
  rewrite (resource select (reveal w) h p model s) as (resource select actual h p model s);
  unfold (resource select actual h p model s);
  let ops = operations select actual;
  rewrite each (operations select actual) as ops;
  let result = ops.value actual.value h #p #model #s;
  rewrite each ops as (operations select actual);
  fold (resource select actual h p model s);
  rewrite (resource select actual h p model s) as (resource select (reveal w) h p model s);
  fold (at select o h w p model s);
  result
}

fn dispose (#m #t:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:selector m t api contents)
  (o h:D.dyn) (#w:erased (C.descriptor m api) { C.supports w }) (#p:perm) (#model:erased m)
  (#s:erased (state t))
  preserves at select o h w p model s
{
  unfold (at select o h w p model s);
  let actual = A.recover #(C.descriptor m api) #w o;
  rewrite (resource select (reveal w) h p model s) as (resource select actual h p model s);
  unfold (resource select actual h p model s);
  let ops = operations select actual;
  rewrite each (operations select actual) as ops;
  ops.dispose actual.value h #p #model #s;
  rewrite each ops as (operations select actual);
  fold (resource select actual h p model s);
  rewrite (resource select actual h p model s) as (resource select (reveal w) h p model s);
  fold (at select o h w p model s);
}

fn release (#m #t:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:selector m t api contents)
  (o h:D.dyn) (#w:erased (C.descriptor m api) { C.supports w }) (#p:perm) (#model:erased m)
  (#s:erased (state t))
  requires at select o h w p model s
  ensures C.base_at o w p model
{
  unfold (at select o h w p model s);
  let actual = A.recover #(C.descriptor m api) #w o;
  rewrite (resource select (reveal w) h p model s) as (resource select actual h p model s);
  unfold (resource select actual h p model s);
  let ops = operations select actual;
  rewrite each (operations select actual) as ops;
  ops.release actual.value h #p #model #s;
  rewrite (actual.owns actual.value p model) as ((reveal w).owns (reveal w).value p model);
  fold (C.source_at o w p model);
  fold (C.base_at o w p model);
}
