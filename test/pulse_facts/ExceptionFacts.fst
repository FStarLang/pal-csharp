// F86, F87: Pulse's native exceptions (FStarLang/FStar#4798), as §19 uses them.
module ExceptionFacts
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module Seq = FStar.Seq

noeq type myex__payload = { code: Int32.t }
exception MyEx of myex__payload
exception SubEx of myex__payload

let is_MyEx (e:exn) : bool = match e with MyEx _ -> true | SubEx _ -> true | _ -> false
let is_SubEx (e:exn) : bool = match e with SubEx _ -> true | _ -> false
let myex_code (e:exn{is_MyEx e}) : Int32.t = match e with MyEx p -> p.code | SubEx p -> p.code
let new_MyEx (c:Int32.t) : (e:exn{is_MyEx e}) = MyEx { code = c }


// P1: non-divergent fn that raises from a branch, statement-position if.
fn check (x:Int32.t)
  requires emp
  ensures pure (Int32.v x >= 0)
  raises (fun (ex:exn) -> pure (is_MyEx ex /\ myex_code ex == 7l /\ Int32.v x < 0))
{
  if (Int32.lt x 0l) {
    let t = new_MyEx 7l;
    raise t
  } else { () };
  ()
}

// P2: raising inside a loop with an array resource.
fn scan (a:A.array Int32.t) (n:SizeT.t) (#s:erased (Seq.seq Int32.t)) (#p:perm)
  requires A.pts_to a #p s ** pure (SizeT.v n == Seq.length s)
  ensures A.pts_to a #p s ** pure (forall (j:nat). j < Seq.length s ==> Int32.v (Seq.index s j) >= 0)
  raises (fun (ex:exn) -> A.pts_to a #p s ** pure (is_MyEx ex /\ (exists (j:nat). j < Seq.length s /\ Int32.v (Seq.index s j) < 0)))
{
  let mut i = 0sz;
  while (SizeT.lt !i n)
    invariant exists* vi. R.pts_to i vi ** A.pts_to a #p s ** pure (SizeT.v vi <= Seq.length s /\ (forall (j:nat). j < SizeT.v vi ==> Int32.v (Seq.index s j) >= 0))
    decreases (SizeT.v n - SizeT.v !i)
  {
    let v = a.(!i);
    if (Int32.lt v 0l) {
      let t = new_MyEx 1l;
      raise t
    } else { () };
    i := SizeT.add !i 1sz;
  };
  ()
}

// P3: try/catch with variable pattern, partial handling via if/else raise, frame of a cell.
fn caller (x:Int32.t)
  requires emp
  returns r:Int32.t
  ensures pure (Int32.v x >= 0 ==> r == 1l)
  raises (fun (ex:exn) -> pure False)
{
  let mut res = 0l;
  try
    ensures exists* v. R.pts_to res v ** pure (Int32.v x >= 0 ==> v == 1l)
    raises (fun (ex:exn) -> exists* v. R.pts_to res v ** pure (is_MyEx ex /\ myex_code ex == 7l /\ Int32.v x < 0))
  {
    check x;
    res := 1l;
  }
  catch {
    ex -> {
      if (is_MyEx ex) {
        res := 2l
      } else {
        raise ex
      }
    }
  };
  !res
}

// P4 (F86): a `try` is not framed. `r` is named in neither clause, so it is lost.
[@@expect_failure]
fn framed (x:Int32.t) (r:R.ref Int32.t)
  requires R.pts_to r 5l
  ensures R.pts_to r 5l
{
  try
    raises (fun (ex:exn) -> pure (is_MyEx ex))
  {
    check x;
  }
  catch {
    ex -> { if (is_MyEx ex) { () } else { raise ex } }
  };
  ()
}
