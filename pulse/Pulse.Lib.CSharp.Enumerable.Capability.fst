module Pulse.Lib.CSharp.Enumerable.Capability
#lang-pulse

open Pulse
module C = Pulse.Lib.CSharp.Capability
module S = Pulse.Lib.CSharp.Enumerable.Source
module A = Pulse.Lib.CSharp.Array.Base
module D = FStar.Dyn
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

// A descriptor has a large existential implementation type. Store its dyn
// identity, not the descriptor itself, in the Type0 enumerable. Its one ghost
// witness is shared by casts and slot calls; no mkdyn injectivity is needed.
let resource (#m:Type0) (#api:C.api_kind m)
  (w:erased (C.descriptor m api)) (o:D.dyn) (p:perm) (model:m) : slprop =
  C.source_at o w p (hide model)

let pts_to (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (w:erased (C.descriptor m api)) (p:perm) (model:erased m) : slprop =
  S.pts_to (resource w) contents e p model

ghost
fn open_source (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires pts_to contents e w p model
  ensures C.source_at (S.source e) w p model ** S.opened contents e p model
{
  unfold (pts_to contents e w p model);
  S.open_source (resource w) contents e;
  unfold (resource w (S.source e) p model);
}

ghost
fn close_source (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires C.source_at (S.source e) w p model ** S.opened contents e p model
  ensures pts_to contents e w p model
{
  fold (resource w (S.source e) p model);
  S.close_source (resource w) contents e;
  fold (pts_to contents e w p model);
}

let snapshot_receipt (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (w:erased (C.descriptor m api)) (p:perm) (model:erased m) : slprop =
  S.snapshot_receipt (resource w) contents e p model

ghost
fn forward_snapshot (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires pts_to contents e w p model
  ensures snapshot_receipt contents e w p model **
    Pulse.Lib.CSharp.Enumerable.pts_to e.snapshot #p (contents model)
{
  unfold (pts_to contents e w p model);
  S.forward_snapshot (resource w) contents e;
  fold (snapshot_receipt contents e w p model);
}

ghost
fn restore_snapshot (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires snapshot_receipt contents e w p model **
    Pulse.Lib.CSharp.Enumerable.pts_to e.snapshot #p (contents model)
  ensures pts_to contents e w p model
{
  unfold (snapshot_receipt contents e w p model);
  S.restore_snapshot (resource w) contents e;
  fold (pts_to contents e w p model);
}

ghost
fn lend (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (o:D.dyn) (arr:A.array t) (coll:bool)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires C.source_at o w p model ** A.pts_to arr #p (contents model)
  ensures pts_to contents (S.view o arr coll) w p model
{
  fold (resource w o p model);
  S.lend (resource w) contents o arr coll;
  fold (pts_to contents (S.view o arr coll) w p model);
}

ghost
fn unlend (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (o:D.dyn) (arr:A.array t) (coll:bool)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  requires pts_to contents (S.view o arr coll) w p model
  ensures C.source_at o w p model ** A.pts_to arr #p (contents model)
{
  unfold (pts_to contents (S.view o arr coll) w p model);
  S.unlend (resource w) contents o arr coll;
  unfold (resource w o p model);
}

// Nominal installation must establish the actual descriptor and its slots.
// Missing evidence for an unknown subclass is not evidence for a None slot.
fn cast (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  preserves pts_to contents e w p model
  returns result:option D.dyn
  ensures pure (result == (if C.supports w then Some (S.source e) else None))
{
  unfold (pts_to contents e w p model);
  S.open_source (resource w) contents e;
  unfold (resource w (S.source e) p model);
  let result = C.cast (S.source e);
  fold (resource w (S.source e) p model);
  S.close_source (resource w) contents e;
  fold (pts_to contents e w p model);
  result
}

// Boolean class-test form of the same source-retaining cast.
fn pts_to_len (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  preserves pts_to contents e w p model
  ensures pure (Seq.length (contents model) < pow2 31)
{
  unfold (pts_to contents e w p model);
  S.pts_to_len (resource w) contents e;
  fold (pts_to contents e w p model);
}

fn matches (#t #m:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (e:enumerable t)
  (#w:erased (C.descriptor m api)) (#p:perm) (#model:erased m)
  preserves pts_to contents e w p model
  returns result:bool
  ensures pure (result == C.supports w)
{
  let result = cast contents e;
  Some? result
}

// Reuse the same checked reader for Count, comparers or a record of scalar
// observations. The snapshot stays owned while the ACTUAL implementation runs.
fn read (#t #m #r:Type0) (#api:C.api_kind m)
  (contents:m -> Seq.seq t) (post:m -> r -> prop) (select:C.reader m r api post)
  (e:enumerable t) (#w:erased (C.descriptor m api) { C.supports w })
  (#p:perm) (#model:erased m)
  preserves pts_to contents e w p model
  returns result:r
  ensures pure (post model result)
{
  unfold (pts_to contents e w p model);
  S.open_source (resource w) contents e;
  unfold (resource w (S.source e) p model);
  C.open_base (S.source e);
  let result = C.read post select (S.source e);
  C.close_base (S.source e);
  fold (resource w (S.source e) p model);
  S.close_source (resource w) contents e;
  fold (pts_to contents e w p model);
  result
}

