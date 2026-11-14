module SortedSetInductive.Item
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module O = SortedSetInductive.Ownership
module H = SortedSetInductive.RetainedHolder
module Q = SortedSetInductive.StateOwnerRead
module S = Class_SortedSet
module I32 = FStar.Int32

#set-options "--z3rlimit 10"

let holder_snapshot (a: Type0) = S.class_SortedSet__raw a

unfold let with_state (#a: Type0) (r: holder_snapshot a) (payload: H.payload a) =
  { r with S.fld_ownershipState = H.state_of payload }

unfold let raw (#a: Type0) (set: S.class_SortedSet a) (r: holder_snapshot a) =
  B.pts_to set r

unfold let state_owner (#a: Type0) (r: holder_snapshot a) (payload: H.payload a) =
  O.owner r.S.fld_root (H.state_of payload) 1.0R

let matches (#a: Type0) (r: holder_snapshot a) (payload: H.payload a)
    (m: S.class_SortedSet__model a) =
  Q.matches r.S.fld_root (H.state_of payload) r.S.fld_comparer
    (I32.v r.S.fld_count) (I32.v r.S.fld_version) m

let pending (#a: Type0) (set: S.class_SortedSet a) (r: holder_snapshot a)
    (payload: H.payload a) (m: S.class_SortedSet__model a) =
  raw set r ** state_owner r payload ** pure (matches r payload m)

ghost fn open_pending (#a: Type0) (set: S.class_SortedSet a) (r: holder_snapshot a)
    (payload: H.payload a) (m: S.class_SortedSet__model a)
  requires pending set r payload m
  ensures raw set r ** state_owner r payload ** pure (matches r payload m)
{
  unfold (pending set r payload m);
}

// The stateful C# helper must perform this exact record update before calling
// this closure. This lemma neither writes a box nor silently changes its index.
ghost fn close_committed (#a: Type0) (set: S.class_SortedSet a) (r: holder_snapshot a)
    (payload: H.payload a) (m: S.class_SortedSet__model a)
  requires raw set (with_state r payload) ** state_owner r payload ** pure (matches r payload m)
  ensures S.class_SortedSet__inv set m
{
  unfold (raw set (with_state r payload));
  unfold (state_owner r payload);
  fold (S.class_SortedSet__inv set m);
}
