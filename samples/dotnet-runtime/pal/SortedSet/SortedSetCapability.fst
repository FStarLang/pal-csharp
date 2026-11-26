module SortedSetCapability
#lang-pulse

// Checked observation adapters over the real generated implementations.
// These are not yet installed by the C# enumerable frontend. In particular no
// enumeration capability is asserted here: the checked view iterator is not
// yet connected to this descriptor.
open Pulse
module C = Pulse.Lib.CSharp.Capability
module D = FStar.Dyn
module R = Pulse.Lib.Reference
module I32 = FStar.Int32
module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module RW = Pulse.Lib.CSharp.RangeWalk
module SS = Class_SortedSet
module V = Struct_SortedSet_TreeSubSet

#set-options "--z3rlimit 10"

noeq type logical (t:Type0) = {
  items: Seq.seq t;
  comparer: O.comparer t;
}

noeq type slots (t i:Type0) (owns: i -> perm -> logical t -> slprop) = {
  count: (x:i -> #p:perm -> #m:erased (logical t) ->
    stt I32.t (owns x p m)
      (fun result -> owns x p m ** pure (I32.v result == Seq.length (reveal m).items)));
  order: (x:i -> #p:perm -> #m:erased (logical t) ->
    stt (O.comparer t) (owns x p m)
      (fun result -> owns x p m ** pure (result == (reveal m).comparer)));
}

let exact_owns (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (x:SS.class_SortedSet t) (p:perm) (m:logical t) : slprop =
  SS.class_SortedSet__inv x #p saved **
  pure (Seq.equal m.items (SS.spec_SortedSet_SpecItems saved) /\
        m.comparer == SS.spec_SortedSet_SpecComparer saved)

fn exact_count (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (x:SS.class_SortedSet t) (#p:perm) (#m:erased (logical t))
  preserves exact_owns saved x p m
  returns result:I32.t
  ensures pure (I32.v result == Seq.length (reveal m).items)
{
  unfold (exact_owns saved x p m);
  let result = Func_SortedSet_Count.func_SortedSet_Count t x;
  fold (exact_owns saved x p m);
  result
}

fn exact_order (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (x:SS.class_SortedSet t) (#p:perm) (#m:erased (logical t))
  preserves exact_owns saved x p m
  returns result:O.comparer t
  ensures pure (result == (reveal m).comparer)
{
  unfold (exact_owns saved x p m);
  let result = Func_SortedSet_Comparer.func_SortedSet_Comparer t x;
  fold (exact_owns saved x p m);
  result
}

// Only the actual source tree is owned at Class_SortedSet.inv. The view itself
// has a DIFFERENT representation and owns its exclusive mutable cache cell.
// Its full underlying model is retained even though the logical base projection
// contains only the filtered sequence and comparer.
noeq type view_handle (t:Type0) = {
  tree: SS.class_SortedSet t;
  state: R.ref (V.struct_SortedSet_TreeSubSet t);
}

let same_bounds (#t:Type0) (a b:V.struct_SortedSet_TreeSubSet t) : prop =
  a.V.fld__min == b.V.fld__min /\ a.V.fld__max == b.V.fld__max /\
  a.V.fld__lBoundActive == b.V.fld__lBoundActive /\
  a.V.fld__uBoundActive == b.V.fld__uBoundActive

let filtered (#t:Type0) (saved:SS.class_SortedSet__model t)
  (v:V.struct_SortedSet_TreeSubSet t) =
  RW.filter (SS.spec_SortedSet_SpecComparer saved)
    v.V.fld__min v.V.fld__max v.V.fld__lBoundActive v.V.fld__uBoundActive
    (SS.spec_SortedSet_SpecItems saved)

let coherent (#t:Type0) (saved:SS.class_SortedSet__model t)
  (v:V.struct_SortedSet_TreeSubSet t) : prop =
  v.V.fld_comparer == SS.spec_SortedSet_SpecComparer saved /\
  (I32.v v.V.fld_version == SS.spec_SortedSet_SpecVersion saved ==>
    SortedSetInductive.Read.view_root (SS.spec_SortedSet_SpecLabels saved)
      (SS.spec_SortedSet_SpecComparer saved) v.V.fld_root (I32.v v.V.fld__rootLevel)
      v.V.fld__min v.V.fld__max v.V.fld__lBoundActive v.V.fld__uBoundActive) /\
  (I32.v v.V.fld__countVersion == SS.spec_SortedSet_SpecVersion saved ==>
    I32.v v.V.fld_count == Seq.length (filtered saved v))

let view_owns (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (bounds:erased (V.struct_SortedSet_TreeSubSet t))
  (x:view_handle t) (p:perm) (m:logical t) : slprop =
  SS.class_SortedSet__inv x.tree #p saved **
  (exists* (v:V.struct_SortedSet_TreeSubSet t).
    R.pts_to x.state v **
    pure (v.V.fld__underlying == x.tree /\ same_bounds v bounds /\ coherent saved v)) **
  pure (Seq.equal m.items (filtered saved bounds) /\
    m.comparer == SS.spec_SortedSet_SpecComparer saved)

fn view_count (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (bounds:erased (V.struct_SortedSet_TreeSubSet t))
  (x:view_handle t) (#p:perm) (#m:erased (logical t))
  preserves view_owns saved bounds x p m
  returns result:I32.t
  ensures pure (I32.v result == Seq.length (reveal m).items)
{
  unfold (view_owns saved bounds x p m);
  with v. _;
  let result = Func_TreeSubSet_at_SortedSet_Count.func_TreeSubSet_at_SortedSet_Count t x.tree x.state;
  with after. _;
  fold (view_owns saved bounds x p m);
  result
}

fn view_order (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (bounds:erased (V.struct_SortedSet_TreeSubSet t))
  (x:view_handle t) (#p:perm) (#m:erased (logical t))
  preserves view_owns saved bounds x p m
  returns result:O.comparer t
  ensures pure (result == (reveal m).comparer)
{
  unfold (view_owns saved bounds x p m);
  with v. _;
  let result = Func_TreeSubSet_at_SortedSet_Comparer.func_TreeSubSet_at_SortedSet_Comparer t x.tree x.state;
  with after. _;
  fold (view_owns saved bounds x p m);
  result
}

let exact_descriptor (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (x:SS.class_SortedSet t) : C.descriptor (logical t) (slots t) = {
  impl = SS.class_SortedSet t;
  owns = exact_owns saved;
  value = x;
  base = Some { count = exact_count saved; order = exact_order saved };
}

let view_descriptor (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (bounds:erased (V.struct_SortedSet_TreeSubSet t))
  (x:view_handle t) : C.descriptor (logical t) (slots t) = {
  impl = view_handle t;
  owns = view_owns saved bounds;
  value = x;
  base = Some { count = view_count saved bounds; order = view_order saved bounds };
}

let count_post (#t:Type0) (m:logical t) (result:I32.t) : prop =
  I32.v result == Seq.length m.items

let select_count (#t:Type0) (i:Type0) (owns:i -> perm -> logical t -> slprop)
  (v:slots t i owns) = v.count

fn count_base (#t:Type0) (o:D.dyn)
  (#w:erased (C.descriptor (logical t) (slots t))) (#p:perm) (#m:erased (logical t))
  preserves C.base_at o w p m
  returns result:I32.t
  ensures pure (I32.v result == Seq.length (reveal m).items)
{
  let result = C.read count_post select_count o;
  result
}

fn actual_view_dispatch (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
  (bounds:erased (V.struct_SortedSet_TreeSubSet t))
  (x:view_handle t) (#p:perm) (#m:erased (logical t))
  preserves view_owns saved bounds x p m
  returns result:I32.t
  ensures pure (I32.v result == Seq.length (reveal m).items)
{
  let w = view_descriptor saved bounds x;
  let o = D.mkdyn w;
  rewrite (view_owns saved bounds x p m) as (w.owns w.value p m);
  fold (C.source_at o (hide w) p m);
  let cast = C.cast o;
  match cast {
    None -> { unreachable (); }
    Some same -> {
      assert pure (same == o);
      rewrite each o as same;
      C.open_base same;
      let result = count_base same;
      C.close_base same;
      unfold (C.source_at same (hide w) p m);
      rewrite (w.owns w.value p m) as (view_owns saved bounds x p m);
      result
    }
  }

}

  // The source tree's Count is NOT the view's Count. Even though that tree is a
  // perfectly valid ordinary SortedSet, installing its implementation in the
  // view's slot cannot establish the view projection's contract.
  [@@expect_failure]
  fn wrong_view_dispatch (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
    (bounds:erased (V.struct_SortedSet_TreeSubSet t))
    (x:view_handle t) (#p:perm) (#m:erased (logical t))
    preserves view_owns saved bounds x p m
    returns result:I32.t
    ensures pure (I32.v result == Seq.length (reveal m).items)
  {
    unfold (view_owns saved bounds x p m);
    let result = Func_SortedSet_Count.func_SortedSet_Count t x.tree;
    fold (view_owns saved bounds x p m);
    result
  }

  // The tree's permission may be fractional, but the mutable view cache remains
  // exclusive. Abstract base dispatch does not create a second copy of it.
  [@@expect_failure]
  ghost
  fn duplicate_view (#t:Type0) (saved:erased (SS.class_SortedSet__model t))
    (bounds:erased (V.struct_SortedSet_TreeSubSet t))
    (x:view_handle t) (#p:perm) (#m:erased (logical t))
    requires view_owns saved bounds x p m
    ensures view_owns saved bounds x p m ** view_owns saved bounds x p m
  {
  }
