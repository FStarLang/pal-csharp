module PlainReturns
#lang-pulse
open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module C = Class_CallbackCell

let held (#a: Type0) (cell: C.class_CallbackCell__opt a)
    (snapshot: C.class_CallbackCell__raw a) =
  if B.is_null cell then pure True else B.pts_to cell snapshot

ghost fn reindex (#a: Type0) (old cell: C.class_CallbackCell__opt a)
    (snapshot: C.class_CallbackCell__raw a)
  requires held old snapshot ** pure (old == cell)
  ensures held cell snapshot
{
  rewrite (held old snapshot) as (held cell snapshot);
}
