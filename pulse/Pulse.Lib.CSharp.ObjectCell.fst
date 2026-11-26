module Pulse.Lib.CSharp.ObjectCell
#lang-pulse

// A mutable local owns either no object or one object model. As with ArrayCell,
// replacement and scope exit leave unreachable objects to the CLR garbage collector.
open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference

let nonnull (r: Type0) = x: B.box r { not (B.is_null x) }
let owner (r m: Type0) = nonnull r -> m -> slprop

let nullable_at (#r #m: Type0) (inv: owner r m) (x: B.box r) (v: option m) : slprop =
  if B.is_null x then pure (v == None)
  else exists* model. pure (v == Some model) ** inv x model

let pts_to (#r #m: Type0) (inv: owner r m) (c: R.ref (B.box r)) (v: option m) : slprop =
  exists* x. R.pts_to c x ** nullable_at inv x v

ghost fn init (#r #m: Type0) (inv: owner r m) (c: R.ref (B.box r))
  requires R.pts_to c (B.null #r)
  ensures pts_to inv c None
{
  assert (pure (B.is_null (B.null #r)));
  rewrite (pure True) as (nullable_at inv (B.null #r) None);
  fold (pts_to inv c None);
}

ghost fn shape (#r #m: Type0) (inv: owner r m) (x: B.box r) (v: option m)
  preserves nullable_at inv x v
  ensures pure (B.is_null x == None? v)
{
  if B.is_null x {
    rewrite (nullable_at inv x v) as (pure (v == None));
    assert (pure (B.is_null x == None? v));
    rewrite (pure (v == None)) as (nullable_at inv x v);
  } else {
    rewrite (nullable_at inv x v) as (exists* model. pure (v == Some model) ** inv x model);
    assert (pure (B.is_null x == None? v));
    rewrite (exists* model. pure (v == Some model) ** inv x model) as (nullable_at inv x v);
  }
}

fn is_null (#r #m: Type0) (inv: owner r m) (c: R.ref (B.box r)) (#v: erased (option m))
  preserves pts_to inv c v
  returns result: bool
  ensures pure (result == None? v)
{
  unfold (pts_to inv c v);
  let x = !c;
  shape inv x v;
  let result = B.is_null x;
  fold (pts_to inv c v);
  result
}

ghost fn open_nonnull (#r #m: Type0) (inv: owner r m) (x: nonnull r)
    (v: option m { Some? v })
  requires nullable_at inv x v
  ensures inv x (Some?.v v)
{
  rewrite (nullable_at inv x v) as (exists* model. pure (v == Some model) ** inv x model);
  with model. assert (inv x model);
  assert (pure (Some?.v v == model));
  rewrite (inv x model) as (inv x (Some?.v v));
}

fn take (#r #m: Type0) (inv: owner r m) (c: R.ref (B.box r))
    (#v: erased (option m) { Some? v })
  requires pts_to inv c v
  returns x: nonnull r
  ensures R.pts_to c x ** inv x (Some?.v v)
{
  unfold (pts_to inv c v);
  let x = !c;
  shape inv x v;
  assert (pure (not (B.is_null x)));
  open_nonnull inv x v;
  x
}

ghost fn put (#r #m: Type0) (inv: owner r m) (c: R.ref (B.box r))
    (x: nonnull r) (v: m)
  requires R.pts_to c x ** inv x v
  ensures pts_to inv c (Some v)
{
  assert (exists* model. pure (Some v == Some model) ** inv x model);
  rewrite (exists* model. pure (Some v == Some model) ** inv x model)
    as (nullable_at inv x (Some v));
  fold (pts_to inv c (Some v));
}

fn set (#r #m: Type0) (inv: owner r m) (c: R.ref (B.box r))
    (x: nonnull r) (#before: erased (option m)) (#after: erased m)
  requires pts_to inv c before ** inv x after
  ensures pts_to inv c (Some after)
{
  unfold (pts_to inv c before);
  with previous. assert (R.pts_to c previous ** nullable_at inv previous before);
  drop_ (nullable_at inv previous before);
  c := x;
  put inv c x after;
}

ghost fn release (#r #m: Type0) (inv: owner r m) (c: R.ref (B.box r)) (#v: option m)
  requires pts_to inv c v
  ensures exists* x. R.pts_to c x
{
  unfold (pts_to inv c v);
  with x. assert (R.pts_to c x ** nullable_at inv x v);
  drop_ (nullable_at inv x v);
}
