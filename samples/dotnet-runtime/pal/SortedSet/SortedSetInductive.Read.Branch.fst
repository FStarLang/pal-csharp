module SortedSetInductive.Read.Branch
#lang-pulse
open Pulse.Lib.Pervasives
module S = Class_SortedSet
module N = Class_Node
module O = SortedSetInductive.Ownership
module R = SortedSetInductive.Read

#set-options "--z3rlimit 5"

// Both branches retain all permissions; the interface hides only their case split.
let handle_or_closed (#a: Type0) (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool) =
  if returned then R.inv owner snapshot p else R.handle_window h t x p

[@@pulse_intro]
ghost fn returned_handle (#a: Type0) (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires R.inv owner snapshot p ** pure returned
  ensures handle_or_closed owner snapshot h t x p returned
{
  rewrite (R.inv owner snapshot p) as (handle_or_closed owner snapshot h t x p returned);
}

[@@pulse_intro]
ghost fn continuing_handle (#a: Type0) (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires R.handle_window h t x p ** pure (~returned)
  ensures handle_or_closed owner snapshot h t x p returned
{
  rewrite (R.handle_window h t x p) as (handle_or_closed owner snapshot h t x p returned);
}

[@@pulse_intro]
ghost fn returned_handle_inv (#a: Type0) (owner: S.class_SortedSet a)
    (expected: S.class_SortedSet__model a) (p: perm)
  requires exists* (snapshot: S.class_SortedSet__model a) (h: R.handle a)
    (t: O.tree a) (x: N.class_Node__opt a) (returned: bool).
    handle_or_closed owner snapshot h t x p returned ** pure (returned /\ snapshot == expected)
  // Use the actual predicate head, not the Read.inv alias, for introduction lookup.
  ensures S.class_SortedSet__inv owner #p expected
{
  with snapshot h t x returned.
    assert (handle_or_closed owner snapshot h t x p returned);
  rewrite (handle_or_closed owner snapshot h t x p returned) as (R.inv owner expected p);
}

ghost fn continuing_handle_window (#a: Type0) (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires handle_or_closed owner snapshot h t x p returned ** pure (~returned)
  ensures R.handle_window h t x p
{
  rewrite (handle_or_closed owner snapshot h t x p returned) as (R.handle_window h t x p);
}
