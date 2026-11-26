module Pulse.Lib.CSharp.Enumerable.Iterator
#lang-pulse
open Pulse
module C = Pulse.Lib.CSharp.Capability
module I = Pulse.Lib.CSharp.Capability.Iterator
module E = Pulse.Lib.CSharp.Enumerable.Capability
module S = Pulse.Lib.CSharp.Enumerable.Source
module WP = Pulse.Lib.WithPure
module D = FStar.Dyn
module Seq = FStar.Seq
#set-options "--z3rlimit 10"

let body (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:I.selector m t api contents)
  (e:E.enumerable t) (h:D.dyn) (w:erased (C.descriptor m api)) (p:perm)
  (model:erased m) (s:erased (I.state t)) (_:squash (C.supports w)) : slprop =
  S.opened contents e p model ** I.at select (S.source e) h w p model s

let at (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:I.selector m t api contents)
  (e:E.enumerable t) (h:D.dyn) (w:erased (C.descriptor m api)) (p:perm)
  (model:erased m) (s:erased (I.state t)) : slprop =
  WP.with_pure (C.supports w) (body contents select e h w p model s)

fn start (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:I.selector m t api contents)
  (e:E.enumerable t) (#w:erased (C.descriptor m api) { C.supports w })
  (#p:perm) (#model:erased m)
  requires E.pts_to contents e w p model
  returns h:D.dyn
  ensures at contents select e h w p model (hide (I.initial (contents model)))
{
  E.open_source contents e;
  C.open_base (S.source e);
  let h = I.start contents select (S.source e) #w #p #model;
  fold (body contents select e h w p model (hide (I.initial (contents model))) ());
  WP.intro_with_pure (C.supports w)
    (body contents select e h w p model (hide (I.initial (contents model)))) ();
  fold (at contents select e h w p model (hide (I.initial (contents model))));
  h
}

fn next (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:I.selector m t api contents)
  (e:E.enumerable t) (h:D.dyn) (#w:erased (C.descriptor m api))
  (#p:perm) (#model:erased m) (#s:erased (I.state t))
  requires at contents select e h w p model s
  returns result:bool
  ensures at contents select e h w p model (hide (I.step s)) ** pure (result == I.moves s)
{
  unfold (at contents select e h w p model s);
  WP.elim_with_pure (C.supports w) (body contents select e h w p model s);
  unfold (body contents select e h w p model s ());
  let result = I.next contents select (S.source e) h #w #p #model #s;
  fold (body contents select e h w p model (hide (I.step s)) ());
  WP.intro_with_pure (C.supports w) (body contents select e h w p model (hide (I.step s))) ();
  fold (at contents select e h w p model (hide (I.step s)));
  result
}

fn value (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:I.selector m t api contents)
  (e:E.enumerable t) (h:D.dyn) (#w:erased (C.descriptor m api))
  (#p:perm) (#model:erased m) (#s:erased (I.state t) { I.valid s })
  preserves at contents select e h w p model s
  returns result:t
  ensures pure (result == Seq.index (reveal s).I.current 0)
{
  unfold (at contents select e h w p model s);
  WP.elim_with_pure (C.supports w) (body contents select e h w p model s);
  unfold (body contents select e h w p model s ());
  let result = I.value contents select (S.source e) h #w #p #model #s;
  fold (body contents select e h w p model s ());
  WP.intro_with_pure (C.supports w) (body contents select e h w p model s) ();
  fold (at contents select e h w p model s);
  result
}

fn dispose (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:I.selector m t api contents)
  (e:E.enumerable t) (h:D.dyn) (#w:erased (C.descriptor m api))
  (#p:perm) (#model:erased m) (#s:erased (I.state t))
  preserves at contents select e h w p model s
{
  unfold (at contents select e h w p model s);
  WP.elim_with_pure (C.supports w) (body contents select e h w p model s);
  unfold (body contents select e h w p model s ());
  I.dispose contents select (S.source e) h #w #p #model #s;
  fold (body contents select e h w p model s ());
  WP.intro_with_pure (C.supports w) (body contents select e h w p model s) ();
  fold (at contents select e h w p model s);
}

fn release (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (select:I.selector m t api contents)
  (e:E.enumerable t) (h:D.dyn) (#w:erased (C.descriptor m api))
  (#p:perm) (#model:erased m) (#s:erased (I.state t))
  requires at contents select e h w p model s
  ensures E.pts_to contents e w p model
{
  unfold (at contents select e h w p model s);
  WP.elim_with_pure (C.supports w) (body contents select e h w p model s);
  unfold (body contents select e h w p model s ());
  I.release contents select (S.source e) h #w #p #model #s;
  C.close_base (S.source e);
  E.close_source contents e;
}
