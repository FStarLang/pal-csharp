module SortedSetInductive.Read.BranchClient
#lang-pulse
open Pulse.Lib.Pervasives
module S = Class_SortedSet
module N = Class_Node
module O = SortedSetInductive.Ownership
module R = SortedSetInductive.Read
module H = SortedSetInductive.Read.Branch
module EQ = Pulse.Lib.CSharp.EqualityModel
open SortedSetInductive.Read.Branch

#set-options "--z3rlimit 5"

ghost fn closed (#a: Type0) {| equality_a: EQ.has_equality a |} (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires R.inv owner snapshot p ** pure returned
  ensures H.handle_or_closed owner snapshot h t x p returned
{
  H.returned_handle owner snapshot h t x p returned;
}

ghost fn closed_automatic (#a: Type0) {| equality_a: EQ.has_equality a |} (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires R.inv owner snapshot p ** pure returned
  ensures H.handle_or_closed owner snapshot h t x p returned
{
  ();
}

ghost fn conditional (#a: Type0) {| equality_a: EQ.has_equality a |} (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires R.handle_window h t x p ** pure (R.handle_matches h owner snapshot)
  ensures H.handle_or_closed owner snapshot h t x p returned
{
  if returned {
    R.window_from_handle owner snapshot h t x p;
    R.close_window t p;
    R.end_set owner snapshot p;
  } else {
    ();
  }
}

ghost fn restored_automatic (#a: Type0) {| equality_a: EQ.has_equality a |} (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires H.handle_or_closed owner snapshot h t x p returned ** pure returned
  ensures R.inv owner snapshot p
{
  ();
}
