module GhostResultNegative
#lang-pulse
open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module C = Class_ProbeCell

unfold let raw (cell: C.class_ProbeCell) (flag: bool) =
  B.pts_to cell { C.fld_flag = flag }

unfold let sealed (cell: C.class_ProbeCell) =
  exists* flag. raw cell flag

ghost fn unpack (cell: C.class_ProbeCell)
  requires sealed cell
  returns flag: erased bool
  ensures raw cell (reveal flag)
{
  unfold (sealed cell);
  with flag. _;
  hide flag
}
