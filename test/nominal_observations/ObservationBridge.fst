module ObservationBridge
#lang-pulse

open Pulse
module C = Pulse.Lib.CSharp.Capability
module E = Pulse.Lib.CSharp.Enumerable.Capability
module S = Pulse.Lib.CSharp.Enumerable.Source
module A = Pulse.Lib.CSharp.Array.Base
module P = Class_Packet
module V = Struct_Packet_Empty
module O = Pulse.Lib.CSharp.Order
module R = Pulse.Lib.Reference
module D = FStar.Dyn
module I32 = FStar.Int32
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

noeq type logical (t:Type0) = { items:Seq.seq t; order:O.comparer t }
noeq type slots (t i:Type0) (owns:i -> perm -> logical t -> slprop) = {
  count: (x:i -> #p:perm -> #m:erased (logical t) ->
    stt I32.t (owns x p m)
      (fun r -> owns x p m ** pure (I32.v r == Seq.length (reveal m).items)));
  order: (x:i -> #p:perm -> #m:erased (logical t) ->
    stt (O.comparer t) (owns x p m)
      (fun r -> owns x p m ** pure (r == (reveal m).order)));
}
let contents (#t:Type0) (m:logical t) = m.items
let count_post (#t:Type0) (m:logical t) (r:I32.t) = I32.v r == Seq.length m.items
let order_post (#t:Type0) (m:logical t) (r:O.comparer t) = r == m.order
let select_count (#t:Type0) (i:Type0) (owns:i -> perm -> logical t -> slprop)
  (s:slots t i owns) = s.count
let select_order (#t:Type0) (i:Type0) (owns:i -> perm -> logical t -> slprop)
  (s:slots t i owns) = s.order

let exact_owns (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:P.class_Packet t) (p:perm) (m:logical t) : slprop =
  P.class_Packet__inv x #p saved **
  pure (Seq.equal m.items (P.spec_Packet_Items saved) /\ m.order == P.spec_Packet_Order saved)

fn exact_count (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:P.class_Packet t) (#p:perm) (#m:erased (logical t))
  preserves exact_owns saved x p m
  returns result:I32.t
  ensures pure (I32.v result == Seq.length (reveal m).items)
{
  unfold (exact_owns saved x p m);
  let result = Func_Packet_Count.func_Packet_Count t x;
  fold (exact_owns saved x p m);
  result
}

fn exact_order (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:P.class_Packet t) (#p:perm) (#m:erased (logical t))
  preserves exact_owns saved x p m
  returns result:O.comparer t
  ensures pure (result == (reveal m).order)
{
  unfold (exact_owns saved x p m);
  let result = Func_Packet_Comparer.func_Packet_Comparer t x;
  fold (exact_owns saved x p m);
  result
}

noeq type handle (t:Type0) = {
  tree:P.class_Packet t;
  state:R.ref (V.struct_Packet_Empty t);
}

// Cache is existential and may change. The actual source invariant and the
// exclusive view cell are both retained. Source and view comparers may differ.
let view_owns (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:handle t) (p:perm) (m:logical t) : slprop =
  P.class_Packet__inv x.tree #p saved **
  (exists* (v:V.struct_Packet_Empty t).
    R.pts_to x.state v **
    pure (v.V.fld_source == x.tree /\ v.V.fld_selected == m.order)) **
  pure (Seq.equal m.items (Seq.slice (P.spec_Packet_Items saved) 0 0))

fn view_count (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:handle t) (#p:perm) (#m:erased (logical t))
  preserves view_owns saved x p m
  returns result:I32.t
  ensures pure (I32.v result == Seq.length (reveal m).items)
{
  unfold (view_owns saved x p m);
  with v. _;
  let result = Func_Empty_Count.func_Empty_Count t x.tree x.state;
  with after. _;
  fold (view_owns saved x p m);
  result
}

fn view_order (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:handle t) (#p:perm) (#m:erased (logical t))
  preserves view_owns saved x p m
  returns result:O.comparer t
  ensures pure (result == (reveal m).order)
{
  unfold (view_owns saved x p m);
  with v. _;
  let result = Func_Empty_Comparer.func_Empty_Comparer t x.tree x.state;
  with after. _;
  fold (view_owns saved x p m);
  result
}

let view_descriptor (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:handle t) : C.descriptor (logical t) (slots t) = {
  impl = handle t; owns = view_owns saved; value = x;
  base = Some { count = view_count saved; order = view_order saved };
}

let exact_descriptor (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:P.class_Packet t) : C.descriptor (logical t) (slots t) = {
  impl = P.class_Packet t; owns = exact_owns saved; value = x;
  base = Some { count = exact_count saved; order = exact_order saved };
}

fn actual_exact (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:P.class_Packet t) (arr:A.array t) (#p:perm) (#m:erased (logical t))
  preserves exact_owns saved x p m ** A.pts_to arr #p (reveal m).items
  returns result:I32.t
  ensures pure (I32.v result == 1)
{
  let w = exact_descriptor saved x;
  let o = D.mkdyn w;
  rewrite (exact_owns saved x p m) as (w.owns w.value p m);
  fold (C.source_at o (hide w) p m);
  E.lend contents o arr false;
  let hit = E.cast contents (S.view o arr false);
  let again = E.cast contents (S.view o arr false);
  assert pure (hit == Some o /\ again == hit);
  let result = E.read contents count_post select_count (S.view o arr false);
  let comparer = E.read contents order_post select_order (S.view o arr false);
  assert pure (comparer == (reveal m).order);
  E.unlend contents o arr false;
  unfold (C.source_at o (hide w) p m);
  rewrite (w.owns w.value p m) as (exact_owns saved x p m);
  unfold (exact_owns saved x p m);
  fold (exact_owns saved x p m);
  result
}

// Target-relative miss mechanics. CLR disjointness is a separate obligation on
// the installer (tested by classifier/); None is never inferred from absent slots.
fn retained_miss (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:P.class_Packet t) (arr:A.array t) (#p:perm) (#m:erased (logical t))
  preserves exact_owns saved x p m ** A.pts_to arr #p (reveal m).items
  returns result:bool
  ensures pure (result == false)
{
  let w : C.descriptor (logical t) (slots t) = { (exact_descriptor saved x) with C.base = None };
  let o = D.mkdyn w;
  rewrite (exact_owns saved x p m) as (w.owns w.value p m);
  fold (C.source_at o (hide w) p m);
  E.lend contents o arr false;
  let hit = E.cast contents (S.view o arr false);
  E.unlend contents o arr false;
  unfold (C.source_at o (hide w) p m);
  rewrite (w.owns w.value p m) as (exact_owns saved x p m);
  Some? hit
}

// This is an explicit checked adapter client, not a claim that C# enumerable
// lowering already installs this descriptor.
fn actual_view (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:handle t) (arr:A.array t) (#p:perm) (#m:erased (logical t))
  preserves view_owns saved x p m ** A.pts_to arr #p (reveal m).items
  returns result:I32.t
  ensures pure (I32.v result == 0)
{
  let w = view_descriptor saved x;
  let o = D.mkdyn w;
  rewrite (view_owns saved x p m) as (w.owns w.value p m);
  fold (C.source_at o (hide w) p m);
  E.lend contents o arr false;
  let hit = E.cast contents (S.view o arr false);
  match hit {
    None -> { unreachable (); }
    Some same -> {
      assert pure (same == o);
      let result = E.read contents count_post select_count (S.view o arr false);
      let comparer = E.read contents order_post select_order (S.view o arr false);
      assert pure (comparer == (reveal m).order);
      E.unlend contents o arr false;
      unfold (C.source_at o (hide w) p m);
      rewrite (w.owns w.value p m) as (view_owns saved x p m);
      unfold (view_owns saved x p m);
      fold (view_owns saved x p m);
      result
    }
  }
}

[@@expect_failure]
fn wrong_view_slot (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:handle t) (#p:perm) (#m:erased (logical t))
  preserves view_owns saved x p m
  returns result:I32.t
  ensures pure (I32.v result == Seq.length (reveal m).items)
{
  unfold (view_owns saved x p m);
  let result = Func_Packet_Count.func_Packet_Count t x.tree;
  fold (view_owns saved x p m);
  result
}

[@@expect_failure]
ghost
fn duplicate_view (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:handle t) (#p:perm) (#m:erased (logical t))
  requires view_owns saved x p m
  ensures view_owns saved x p m ** view_owns saved x p m
{ () }

[@@expect_failure]
ghost
fn wrong_snapshot (#t:Type0) (saved:erased (P.class_Packet__model t))
  (x:P.class_Packet t) (arr:A.array t) (#p:perm) (#m:erased (logical t))
  requires exact_owns saved x p m ** A.pts_to arr #p (Seq.empty #t)
  ensures E.pts_to contents (S.view (D.mkdyn (exact_descriptor saved x)) arr false)
    (hide (exact_descriptor saved x)) p m
{
  let w = exact_descriptor saved x;
  let o = D.mkdyn w;
  rewrite (exact_owns saved x p m) as (w.owns w.value p m);
  fold (C.source_at o (hide w) p m);
  E.lend contents o arr false;
}
