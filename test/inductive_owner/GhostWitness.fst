module GhostWitness
#lang-pulse
open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module N = Class_OwnedCell
module O = OwnerCells

// The returned witness is the record actually owned by the input resource.
// No runtime read, default record, choice operator, or new resource is used.
ghost fn unpack (cell: N.class_OwnedCell)
  requires O.cell cell
  returns witness: erased N.class_OwnedCell__raw
  ensures O.raw cell (reveal witness) 1.0R
{
  unfold (O.cell cell);
  with value. _;
  let record = { N.fld_value = value };
  fold (O.raw cell record 1.0R);
  hide record
}

ghost fn unpack_known (cell: N.class_OwnedCell) (expected: FStar.Int32.t)
  requires O.held cell (FStar.Int32.v expected)
  returns witness: erased N.class_OwnedCell__raw
  ensures O.raw cell (reveal witness) 1.0R **
    pure (O.raw_value (reveal witness) == FStar.Int32.v expected)
{
  unfold (O.held cell (FStar.Int32.v expected));
  with value. _;
  let record = { N.fld_value = value };
  fold (O.raw cell record 1.0R);
  hide record
}

ghost fn pack (cell: N.class_OwnedCell) (record: N.class_OwnedCell__raw)
  requires O.raw cell record 1.0R
  ensures O.cell cell
{
  unfold (O.raw cell record 1.0R);
  rewrite (B.pts_to cell record) as (B.pts_to cell { N.fld_value = record.N.fld_value });
  fold (O.cell cell);
}

ghost fn unpack_fraction (cell: N.class_OwnedCell) (expected: FStar.Int32.t) (p: perm)
  requires O.holds cell (FStar.Int32.v expected) p
  returns witness: erased N.class_OwnedCell__raw
  ensures O.raw cell (reveal witness) p **
    pure (O.raw_value (reveal witness) == FStar.Int32.v expected)
{
  unfold (O.holds cell (FStar.Int32.v expected) p);
  with value. _;
  let record = { N.fld_value = value };
  fold (O.raw cell record p);
  hide record
}

ghost fn pack_fraction (cell: N.class_OwnedCell) (record: N.class_OwnedCell__raw)
    (expected: FStar.Int32.t) (p: perm)
  requires O.raw cell record p ** pure (O.raw_value record == FStar.Int32.v expected)
  ensures O.holds cell (FStar.Int32.v expected) p
{
  unfold (O.raw cell record p);
  rewrite (B.pts_to cell #p record) as
    (B.pts_to cell #p { N.fld_value = record.N.fld_value });
  fold (O.holds cell (FStar.Int32.v expected) p);
}
