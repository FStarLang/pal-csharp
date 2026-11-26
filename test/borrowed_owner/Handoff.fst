module Handoff
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
module C = Class_Owner
module B = Pulse.Lib.Box
module M = Struct_OwnerModel

#set-options "--z3rlimit 10"

let identity (b: bool) = b

unfold let inv (#a: Type0) (source: C.class_Owner a) (m: C.class_Owner__model a) (p: perm) =
  C.class_Owner__inv source #p m

unfold let window (#a: Type0) (source alias: C.class_Owner a) (m: C.class_Owner__model a) (p: perm) =
  exists* (r: C.class_Owner__raw a).
    B.pts_to alias #p r ** (B.pts_to alias #p r @==> inv source m p) **
    pure (m == { M.fld_Value = FStar.Int32.v r.C.fld_value; M.fld_Comparer = r.C.fld_comparer })

ghost fn open_window (#a: Type0) (source: C.class_Owner a) (m: C.class_Owner__model a) (p: perm)
  requires inv source m p
  ensures window source source m p
{
  unfold (inv source m p);
  unfold (C.class_Owner__inv source #p m);
  with r. assert (B.pts_to source #p r);
  intro (B.pts_to source #p r @==> inv source m p) #emp fn _ {
    fold (C.class_Owner__inv source #p m);
    fold (inv source m p);
  };
}

ghost fn open_alias (#a: Type0) (source alias: C.class_Owner a) (m: C.class_Owner__model a) (p: perm)
  requires inv source m p ** pure (source == alias)
  ensures window source alias m p
{
  unfold (inv source m p);
  unfold (C.class_Owner__inv source #p m);
  with r. assert (B.pts_to source #p r);
  rewrite (B.pts_to source #p r) as (B.pts_to alias #p r);
  intro (B.pts_to alias #p r @==> inv source m p) #emp fn _ {
    rewrite (B.pts_to alias #p r) as (B.pts_to source #p r);
    fold (C.class_Owner__inv source #p m);
    fold (inv source m p);
  };
}

[@@pulse_intro]
ghost fn close_window (#a: Type0) (source: C.class_Owner a) (m: C.class_Owner__model a) (p: perm)
  requires exists* (alias: C.class_Owner a) (r: C.class_Owner__raw a).
    B.pts_to alias #p r ** (B.pts_to alias #p r @==> inv source m p)
  ensures C.class_Owner__inv source #p m
{
  with alias r. assert (B.pts_to alias #p r ** (B.pts_to alias #p r @==> inv source m p));
  elim (B.pts_to alias #p r) (inv source m p);
  unfold (inv source m p);
}
