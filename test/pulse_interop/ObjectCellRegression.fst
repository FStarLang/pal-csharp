module ObjectCellRegression
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module OC = Pulse.Lib.CSharp.ObjectCell
module I32 = FStar.Int32
module E = Pulse.Lib.CSharp.Exn

let owned (p: OC.nonnull I32.t) (v: I32.t) = B.pts_to p v

fn allocate (value: I32.t)
  requires emp
  returns p: OC.nonnull I32.t
  ensures owned p value
{
  let p = B.alloc value;
  B.pts_to_not_null p;
  fold (owned p value);
  p
}

fn read (cell: Pulse.Lib.Reference.ref (B.box I32.t))
    (#v: erased (option I32.t) { Some? v })
  requires OC.pts_to owned cell v
  returns result: I32.t
  ensures OC.pts_to owned cell (Some result) ** pure (result == Some?.v v)
{
  let p = OC.take owned cell;
  unfold (owned p (Some?.v v));
  let value = B.op_Bang p;
  fold (owned p value);
  OC.put owned cell p value;
  value
}

fn lazy_twice ()
  requires emp
  returns result: I32.t
  ensures pure (I32.v result == 42)
{
  let mut cell = B.null #I32.t;
  OC.init owned cell;
  let missing = OC.is_null owned cell;
  if missing {
    let p = allocate 42l;
    OC.set owned cell p;
  } else { () };
  let missing_again = OC.is_null owned cell;
  if missing_again {
    let p = allocate 0l;
    OC.set owned cell p;
  } else { () };
  let value = read cell;
  OC.release owned cell;
  value
}

fn replace ()
  requires emp
  returns result: I32.t
  ensures pure (I32.v result == 7)
{
  let mut cell = B.null #I32.t;
  OC.init owned cell;
  let first = allocate 42l;
  OC.set owned cell first;
  let second = allocate 7l;
  OC.set owned cell second;
  let value = read cell;
  OC.release owned cell;
  value
}

fn mutate_then_raise (p: OC.nonnull I32.t)
  requires owned p 42l
  ensures pure False
  raises (fun e -> owned p 43l ** pure (e == E.BclException "System.ArgumentException"))
{
  unfold (owned p 42l);
  B.op_Colon_Equals p 43l;
  fold (owned p 43l);
  raise (E.BclException "System.ArgumentException")
}

fn recover ()
  requires emp
  returns result: I32.t
  ensures pure (I32.v result == 43)
{
  let mut cell = B.null #I32.t;
  OC.init owned cell;
  let initial = allocate 42l;
  OC.set owned cell initial;
  let p = OC.take owned cell;
  try
    ensures Pulse.Lib.Reference.pts_to cell p ** owned p 43l
    raises (fun e -> Pulse.Lib.Reference.pts_to cell p ** owned p 43l **
      pure (e == E.BclException "System.ArgumentException"))
  {
    mutate_then_raise p
  } catch {
    e -> { () }
  };
  OC.put owned cell p 43l;
  let value = read cell;
  OC.release owned cell;
  value
}
