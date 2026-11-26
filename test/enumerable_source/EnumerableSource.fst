module EnumerableSource
#lang-pulse

open Pulse
module S = Pulse.Lib.CSharp.Enumerable.Source
module A = Pulse.Lib.CSharp.Array.Base
module CA = Pulse.Lib.CSharp.Array
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

let array_owns (#t: Type0) (a: A.array t) (p: perm) (items: Seq.seq t) : slprop =
  A.pts_to a #p items

let array_contents (#t: Type0) (items: Seq.seq t) : Seq.seq t = items

// Count/CopyTo establishes the source/snapshot correspondence. The source is
// not inferred from the snapshot, and both arrays are returned to their owner.
fn checked_copy (#t: Type0) (src dst: A.array t) (coll: bool)
  (#items #initial: erased (Seq.seq t) { Seq.length items == Seq.length initial })
  requires A.pts_to src items ** A.pts_to dst initial
  returns n: I32.t
  ensures A.pts_to src items ** A.pts_to dst items **
    pure (I32.v n == Seq.length items)
{
  let n = CA.length_i32 src;
  CA.copy src dst n;
  with copied. assert (A.pts_to dst copied);
  Seq.lemma_eq_intro copied (reveal items);
  Seq.lemma_eq_elim copied (reveal items);
  fold (array_owns src 1.0R items);
  S.lend array_owns array_contents src dst coll;
  let e = S.view src dst coll;
  rewrite each (S.view src dst coll) as e;
  assert pure (S.source e == src);
  S.pts_to_len array_owns array_contents e;
  S.open_source array_owns array_contents e;
  unfold (array_owns (S.source e) 1.0R items);
  let again = CA.length_i32 (S.source e);
  fold (array_owns (S.source e) 1.0R items);
  S.close_source array_owns array_contents e;
  rewrite each e as (S.view src dst coll);
  S.unlend array_owns array_contents src dst coll;
  unfold (array_owns src 1.0R items);
  again
}

// The descriptor is preserved, not just the concrete representation of its
// payload. A compiler adapter can instead use its coherent CLR descriptor here.
noeq type cell_source = { tag: bool; cell: B.box I32.t }

let cell_owns (o: cell_source) (p: perm) (v: I32.t) : slprop =
  B.pts_to o.cell #p v

let cell_contents (v: I32.t) : Seq.seq I32.t = Seq.create 1 v

// Real allocation/read/copy/enumeration/free. The caller's snapshot buffer is
// returned, not leaked; the source box is allocated and freed here.
// A runtime tag survives an intervening source read and subsequent enumeration.
fn allocating_client (tag: bool) (a: A.array I32.t)
  (#initial: erased (Seq.seq I32.t) { Seq.length initial == 1 })
  requires A.pts_to a initial
  returns result: bool
  ensures A.pts_to a (Seq.create 1 7l) ** pure (result == true)
{
  let b = B.alloc 7l;
  let value = B.op_Bang b;
  CA.write a 0l value;
  Seq.lemma_eq_intro (Seq.upd (reveal initial) 0 7l) (Seq.create 1 7l);
  Seq.lemma_eq_elim (Seq.upd (reveal initial) 0 7l) (Seq.create 1 7l);
  let o = { tag; cell = b };
  rewrite (B.pts_to b 7l) as (B.pts_to o.cell 7l);
  fold (cell_owns o 1.0R 7l);
  S.lend cell_owns cell_contents o a true;
  let e = S.view o a true;
  rewrite each (S.view o a true) as e;
  assert pure ((S.source e).tag == tag);
  let count = S.count cell_owns cell_contents e;
  assert pure (count == 1l);
  S.open_source cell_owns cell_contents e;
  unfold (cell_owns (S.source e) 1.0R 7l);
  let from_source = B.op_Bang (S.source e).cell;
  fold (cell_owns (S.source e) 1.0R 7l);
  S.close_source cell_owns cell_contents e;
  let mut cursor = 0l;
  let more = S.move_next cell_owns cell_contents e cursor;
  assert pure more;
  let from_snapshot = S.current cell_owns cell_contents e cursor;
  let ended = S.move_next cell_owns cell_contents e cursor;
  assert pure (not ended);
  rewrite each e as (S.view o a true);
  S.unlend cell_owns cell_contents o a true;
  unfold (cell_owns o 1.0R 7l);
  rewrite (B.pts_to o.cell 7l) as (B.pts_to b 7l);
  B.free b;
  I32.eq from_source from_snapshot
}

// The loan cannot be formed from a snapshot with different contents.
[@@expect_failure]
ghost
fn wrong_snapshot (o: cell_source) (a: A.array I32.t)
  requires cell_owns o 1.0R 7l ** A.pts_to a (Seq.create 1 9l)
  ensures S.pts_to cell_owns cell_contents (S.view o a true) 1.0R (hide 7l)
{
  S.lend cell_owns cell_contents o a true;
}

// The source cannot also be handed to a receiver requiring full ownership.
[@@expect_failure]
ghost
fn cannot_keep_source (o: cell_source) (a: A.array I32.t)
  requires cell_owns o 1.0R 7l ** A.pts_to a (Seq.create 1 7l)
  ensures S.pts_to cell_owns cell_contents (S.view o a true) 1.0R (hide 7l) **
    cell_owns o 1.0R 7l
{
  S.lend cell_owns cell_contents o a true;
}

// Opening the source is a resource transfer, not another ownership-producing cast.
[@@expect_failure]
ghost
fn cannot_open_twice (e: S.enumerable I32.t cell_source)
  requires S.pts_to cell_owns cell_contents e 1.0R (hide 7l)
  ensures cell_owns (S.source e) 1.0R 7l ** cell_owns (S.source e) 1.0R 7l
{
  S.open_source cell_owns cell_contents e;
  S.open_source cell_owns cell_contents e;
}

// A source mutation cannot be hidden behind the stale snapshot when re-closing.
[@@expect_failure]
fn cannot_close_changed_source (e: S.enumerable I32.t cell_source)
  requires S.pts_to cell_owns cell_contents e 1.0R (hide 7l)
  ensures S.pts_to cell_owns cell_contents e 1.0R (hide 7l)
{
  S.open_source cell_owns cell_contents e;
  unfold (cell_owns (S.source e) 1.0R 7l);
  B.op_Colon_Equals (S.source e).cell 9l;
  fold (cell_owns (S.source e) 1.0R 9l);
  S.close_source cell_owns cell_contents e;
}
