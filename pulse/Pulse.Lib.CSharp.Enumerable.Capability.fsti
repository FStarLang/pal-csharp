module Pulse.Lib.CSharp.Enumerable.Capability
#lang-pulse
open Pulse
module C = Pulse.Lib.CSharp.Capability
module S = Pulse.Lib.CSharp.Enumerable.Source
module A = Pulse.Lib.CSharp.Array.Base
module D = FStar.Dyn
module Seq = FStar.Seq

let enumerable (t:Type0) = S.enumerable t D.dyn

val pts_to (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (w:erased (C.descriptor m api)) (p:perm) (model:erased m) : slprop

ghost
fn open_source (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires pts_to contents e w p model
  ensures C.source_at (S.source e) w p model ** S.opened contents e p model

ghost
fn close_source (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires C.source_at (S.source e) w p model ** S.opened contents e p model
  ensures pts_to contents e w p model

// During a snapshot-only call the descriptor resource remains in this receipt.
// It cannot be read, cast, or lent a second time until the snapshot returns.
val snapshot_receipt (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (w:erased (C.descriptor m api)) (p:perm) (model:erased m) : slprop

ghost
fn forward_snapshot (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires pts_to contents e w p model
  ensures snapshot_receipt contents e w p model **
    Pulse.Lib.CSharp.Enumerable.pts_to e.snapshot #p (contents model)

ghost
fn restore_snapshot (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires snapshot_receipt contents e w p model **
    Pulse.Lib.CSharp.Enumerable.pts_to e.snapshot #p (contents model)
  ensures pts_to contents e w p model

ghost
fn lend (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (o:D.dyn) (arr:A.array t) (coll:bool)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires C.source_at o w p model ** A.pts_to arr #p (contents model)
  ensures pts_to contents (S.view o arr coll) w p model

ghost
fn unlend (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (o:D.dyn) (arr:A.array t) (coll:bool)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires pts_to contents (S.view o arr coll) w p model
  ensures C.source_at o w p model ** A.pts_to arr #p (contents model)

fn cast (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  preserves pts_to contents e w p model
  returns result:option D.dyn
  ensures pure (result == (if C.supports w then Some (S.source e) else None))

fn pts_to_len (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  preserves pts_to contents e w p model
  ensures pure (Seq.length (contents model) < pow2 31)

fn matches (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  preserves pts_to contents e w p model
  returns result:bool
  ensures pure (result == C.supports w)

fn read (#t #m #r:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (post:m -> r -> prop) (select:C.reader m r api post)
  (e:enumerable t) (#w:erased (C.descriptor m api) { C.supports w })
  (#p:perm) (#model:erased m)
  preserves pts_to contents e w p model
  returns result:r
  ensures pure (post model result)

