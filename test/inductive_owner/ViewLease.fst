module ViewLease
#lang-pulse
open Pulse.Lib.Pervasives
module C = Class_ViewOwner
module B = Pulse.Lib.Box
module M = Struct_ViewOwnerModel

#set-options "--z3rlimit 10"

let observe_model (#a: Type0) (snapshot: C.class_ViewOwner__model a) (value: int)
  : Lemma (requires (C.spec_ViewOwner_Value snapshot == value))
          (ensures (value == C.spec_ViewOwner_Value snapshot)) = ()

let snapshot_of (#a: Type0) (snapshot: C.class_ViewOwner__model a)
  : C.class_ViewOwner__model a = snapshot

unfold let inv (#a: Type0) (owner: C.class_ViewOwner a) (snapshot: C.class_ViewOwner__model a) (p: perm) =
  C.class_ViewOwner__inv owner #p snapshot

let opened (#a: Type0) (owner: C.class_ViewOwner a) (snapshot: C.class_ViewOwner__model a) (p: perm) =
  exists* r. B.pts_to owner #p r **
    pure (snapshot == { M.fld_Value = FStar.Int32.v r.C.fld_value;
                       M.fld_Tag = FStar.Seq.snoc FStar.Seq.empty r.C.fld_marker })

ghost fn begin_read (#a: Type0) (owner: C.class_ViewOwner a) (snapshot: C.class_ViewOwner__model a) (p: perm)
  requires inv owner snapshot p
  ensures opened owner snapshot p
{
  unfold (inv owner snapshot p);
  unfold (C.class_ViewOwner__inv owner #p snapshot);
  fold (opened owner snapshot p);
}

ghost fn end_read (#a: Type0) (owner: C.class_ViewOwner a) (snapshot: C.class_ViewOwner__model a) (p: perm)
  requires opened owner snapshot p
  ensures inv owner snapshot p
{
  unfold (opened owner snapshot p);
  fold (C.class_ViewOwner__inv owner #p snapshot);
  fold (inv owner snapshot p);
}

unfold let closed_or_opened (#a: Type0) (owner: C.class_ViewOwner a)
    (snapshot: C.class_ViewOwner__model a) (p: perm) (closed: bool) =
  if closed then inv owner snapshot p else opened owner snapshot p

ghost fn complete (#a: Type0) (owner: C.class_ViewOwner a)
    (snapshot: C.class_ViewOwner__model a) (p: perm) (closed: bool)
  requires closed_or_opened owner snapshot p closed
  ensures inv owner snapshot p
{
  if closed {
    rewrite (closed_or_opened owner snapshot p closed) as (inv owner snapshot p);
  } else {
    rewrite (closed_or_opened owner snapshot p closed) as (opened owner snapshot p);
    end_read owner snapshot p;
  }
}
