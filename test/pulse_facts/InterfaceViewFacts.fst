module InterfaceViewFacts
#lang-pulse

open Pulse
module D = FStar.Dyn
module B = Pulse.Lib.Box
module A = Pulse.Lib.CSharp.Assumptions
module Array = Pulse.Lib.CSharp.Array.Base
module CA = Pulse.Lib.CSharp.Array
module S = Pulse.Lib.CSharp.Enumerable.Source
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

// A nominal base-class capability. A compiler adapter must install this slot
// exactly for assignable classes, and select their actual virtual implementation.
// Its invariant describes the logical base view, not the base implementation's
// concrete storage. Other source classes may have no such capability.
noeq type descriptor = {
  impl: Type0;
  owns: impl -> perm -> bool -> slprop;
  object: impl;
  enumerate_one: (
    x:impl -> #p:perm -> #m:erased bool ->
    stt bool (owns x p m) (fun result -> owns x p m ** pure (result == reveal m)));
  read_base: option (
    x:impl -> #p:perm -> #m:erased bool ->
    stt bool (owns x p m) (fun result -> owns x p m ** pure (result == reveal m)));
}

let supports_base (w: descriptor) : bool = Some? w.read_base

let source_at (o: D.dyn) (w: erased descriptor) (p: perm) (m: erased bool) : slprop =
  pure (o == D.mkdyn (reveal w)) ** (reveal w).owns (reveal w).object p m

let base_at (o: D.dyn) (w: erased descriptor) (p: perm) (m: erased bool) : slprop =
  source_at o w p m ** pure (supports_base w)

fn as_base (o: D.dyn) (#w: erased descriptor) (#p: perm) (#m: erased bool)
  preserves source_at o w p m
  returns result: option D.dyn
  ensures pure (result == (if supports_base w then Some o else None))
{
  unfold (source_at o w p m);
  let actual = A.recover #descriptor #w o;
  let result = if supports_base actual { Some o } else { None #D.dyn };
  fold (source_at o w p m);
  result
}

ghost
fn open_base (o: D.dyn)
    (#w: erased descriptor { supports_base w }) (#p: perm) (#m: erased bool)
  requires source_at o w p m
  ensures base_at o w p m
{
  fold (base_at o w p m);
}

ghost
fn close_base (o: D.dyn) (#w: erased descriptor) (#p: perm) (#m: erased bool)
  requires base_at o w p m
  ensures source_at o w p m
{
  unfold (base_at o w p m);
}

fn read_through_base (o: D.dyn) (#w: erased descriptor) (#p: perm) (#m: erased bool)
  preserves base_at o w p m
  returns result: bool
  ensures pure (result == reveal m)
{
  unfold (base_at o w p m);
  unfold (source_at o w p m);
  let actual = A.recover #descriptor #w o;
  rewrite ((reveal w).owns (reveal w).object p m) as
    (actual.owns actual.object p m);
  let slot = actual.read_base;
  match slot {
    None -> { unreachable (); }
    Some read -> {
      let result = read actual.object #p #m;
      rewrite (actual.owns actual.object p m) as
        ((reveal w).owns (reveal w).object p m);
      fold (source_at o w p m);
      fold (base_at o w p m);
      result
    }
  }
}

fn read_enumerable (o: D.dyn) (#w: erased descriptor) (#p: perm) (#m: erased bool)
  preserves source_at o w p m
  returns result: bool
  ensures pure (result == reveal m)
{
  unfold (source_at o w p m);
  let actual = A.recover #descriptor #w o;
  rewrite ((reveal w).owns (reveal w).object p m) as
    (actual.owns actual.object p m);
  let read = actual.enumerate_one;
  let result = read actual.object #p #m;
  rewrite (actual.owns actual.object p m) as
    ((reveal w).owns (reveal w).object p m);
  fold (source_at o w p m);
  result
}

let ordinary_owns (x: B.box bool) (p: perm) (m: bool) : slprop =
  B.pts_to x #p m

fn ordinary_read (x: B.box bool) (#p: perm) (#m: erased bool)
  preserves ordinary_owns x p m
  returns result: bool
  ensures pure (result == reveal m)
{
  unfold (ordinary_owns x p m);
  let result = B.op_Bang x;
  fold (ordinary_owns x p m);
  result
}

let derived_owns (x: B.box bool) (p: perm) (m: bool) : slprop =
  B.pts_to x #p (not m)

fn derived_read (x: B.box bool) (#p: perm) (#m: erased bool)
  preserves derived_owns x p m
  returns result: bool
  ensures pure (result == reveal m)
{
  unfold (derived_owns x p m);
  let stored = B.op_Bang x;
  fold (derived_owns x p m);
  not stored
}

let ordinary_descriptor (x: B.box bool) : descriptor = {
  impl = B.box bool;
  owns = ordinary_owns;
  object = x;
  enumerate_one = ordinary_read;
  read_base = Some ordinary_read;
}

let derived_descriptor (x: B.box bool) : descriptor = {
  impl = B.box bool;
  owns = derived_owns;
  object = x;
  enumerate_one = derived_read;
  read_base = Some derived_read;
}

let unrelated_descriptor (x: B.box bool) : descriptor = {
  impl = B.box bool;
  owns = ordinary_owns;
  object = x;
  enumerate_one = ordinary_read;
  read_base = None;
}

fn derived_client (x: B.box bool) (#p: perm) (#m: erased bool)
  preserves derived_owns x p m
  returns result: bool
  ensures pure (result == reveal m)
{
  let w = derived_descriptor x;
  let o = D.mkdyn w;
  rewrite (derived_owns x p m) as (w.owns w.object p m);
  fold (source_at o (hide w) p m);
  let cast = as_base o;
  match cast {
    None -> { unreachable (); }
    Some view -> {
      assert pure (view == o);
      rewrite each o as view;
      open_base view;
      let result = read_through_base view;
      close_base view;
      unfold (source_at view (hide w) p m);
      rewrite (w.owns w.object p m) as (derived_owns x p m);
      result
    }
  }
}

fn unrelated_client (x: B.box bool) (#p: perm) (#m: erased bool)
  preserves ordinary_owns x p m
  returns result: option D.dyn
  ensures pure (result == None)
{
  let w = unrelated_descriptor x;
  let o = D.mkdyn w;
  rewrite (ordinary_owns x p m) as (w.owns w.object p m);
  fold (source_at o (hide w) p m);
  let result = as_base o;
  unfold (source_at o (hide w) p m);
  rewrite (w.owns w.object p m) as (ordinary_owns x p m);
  result
}

// The successful base cast above cannot justify the ordinary implementation's
// representation invariant: the derived getter deliberately interprets it differently.
[@@expect_failure]
ghost
fn cannot_substitute_base_storage (x: B.box bool)
  requires derived_owns x 1.0R true
  ensures ordinary_owns x 1.0R true
{
  unfold (derived_owns x 1.0R true);
  fold (ordinary_owns x 1.0R true);
}

[@@expect_failure]
fn cannot_dispatch_to_base_implementation (x: B.box bool) (#m: erased bool)
  preserves derived_owns x 1.0R m
  returns result: bool
  ensures pure (result == reveal m)
{
  let result = ordinary_read x;
  result
}

let retained_owns (w: erased descriptor) (o: D.dyn) (p: perm) (m: bool) : slprop =
  source_at o w p (hide m)

let contents (m: bool) : Seq.seq bool = Seq.create 1 m

// Both the cast branch and the enumeration branch read the same logical model.
// The snapshot is filled through the actual descriptor's enumeration operation,
// not postulated independently of the source. The source descriptor is retained
// at the same ghost index while the source-retaining loan is opened and closed.
fn cast_or_enumerate (o: D.dyn) (buffer: Array.array bool)
    (#w: erased descriptor) (#m: erased bool)
    (#initial: erased (Seq.seq bool) { Seq.length initial == 1 })
  requires source_at o w 1.0R m ** Array.pts_to buffer initial
  returns result: bool
  ensures source_at o w 1.0R m ** Array.pts_to buffer (contents m) **
    pure (result == reveal m)
{
  let item = read_enumerable o;
  CA.write buffer 0l item;
  Seq.lemma_eq_intro (Seq.upd (reveal initial) 0 item) (contents m);
  Seq.lemma_eq_elim (Seq.upd (reveal initial) 0 item) (contents m);
  fold (retained_owns w o 1.0R m);
  S.lend (retained_owns w) contents o buffer true;
  let e = S.view o buffer true;
  rewrite each (S.view o buffer true) as e;
  S.open_source (retained_owns w) contents e;
  unfold (retained_owns w (S.source e) 1.0R m);
  let mut cursor = 0l;
  let cast = as_base (S.source e);
  let result = if (Some? cast) {
      let cast_object = Some?.v cast;
      assert pure (cast_object == S.source e);
      rewrite each (S.source e) as cast_object;
      open_base cast_object;
      let result = read_through_base cast_object;
      close_base cast_object;
      fold (retained_owns w cast_object 1.0R m);
      rewrite each cast_object as (S.source e);
      S.close_source (retained_owns w) contents e;
      result
    } else {
      fold (retained_owns w (S.source e) 1.0R m);
      S.close_source (retained_owns w) contents e;
      let more = S.move_next (retained_owns w) contents e cursor;
      assert pure more;
      S.current (retained_owns w) contents e cursor
  };
  rewrite each e as (S.view o buffer true);
  S.unlend (retained_owns w) contents o buffer true;
  unfold (retained_owns w o 1.0R m);
  result
}

fn allocating_cast_and_enumeration (derived: bool) (buffer: Array.array bool)
    (#initial: erased (Seq.seq bool) { Seq.length initial == 1 })
  requires Array.pts_to buffer initial
  returns result: bool
  ensures Array.pts_to buffer (contents true) ** pure result
{
  let stored = not derived;
  let x = B.alloc stored;
  let w = if derived { derived_descriptor x } else { unrelated_descriptor x };
  if derived {
    rewrite (B.pts_to x stored) as (B.pts_to x false);
    fold (derived_owns x 1.0R true);
    rewrite (derived_owns x 1.0R true) as (w.owns w.object 1.0R true);
  } else {
    rewrite (B.pts_to x stored) as (B.pts_to x true);
    fold (ordinary_owns x 1.0R true);
    rewrite (ordinary_owns x 1.0R true) as (w.owns w.object 1.0R true);
  };
  let o = D.mkdyn w;
  fold (source_at o (hide w) 1.0R (hide true));
  let result = cast_or_enumerate o buffer;
  unfold (source_at o (hide w) 1.0R (hide true));
  if derived {
    rewrite (w.owns w.object 1.0R true) as (derived_owns x 1.0R true);
    unfold (derived_owns x 1.0R true);
    rewrite (B.pts_to x false) as (B.pts_to x stored);
  } else {
    rewrite (w.owns w.object 1.0R true) as (ordinary_owns x 1.0R true);
    unfold (ordinary_owns x 1.0R true);
    rewrite (B.pts_to x true) as (B.pts_to x stored);
  };
  B.free x;
  result
}
