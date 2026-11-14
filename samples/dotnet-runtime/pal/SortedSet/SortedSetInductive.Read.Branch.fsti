module SortedSetInductive.Read.Branch
#lang-pulse
open Pulse.Lib.Pervasives
module S = Class_SortedSet
module N = Class_Node
module O = SortedSetInductive.Ownership
module R = SortedSetInductive.Read

val handle_or_closed : #a:Type0 -> S.class_SortedSet a ->
  S.class_SortedSet__model a -> R.handle a -> O.tree a ->
  N.class_Node__opt a -> perm -> bool -> slprop

[@@pulse_intro]
ghost fn returned_handle (#a: Type0) (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires R.inv owner snapshot p ** pure returned
  ensures handle_or_closed owner snapshot h t x p returned

[@@pulse_intro]
ghost fn continuing_handle (#a: Type0) (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires R.handle_window h t x p ** pure (~returned)
  ensures handle_or_closed owner snapshot h t x p returned

[@@pulse_intro]
ghost fn returned_handle_inv (#a: Type0) (owner: S.class_SortedSet a)
    (expected: S.class_SortedSet__model a) (p: perm)
  requires exists* (snapshot: S.class_SortedSet__model a) (h: R.handle a)
    (t: O.tree a) (x: N.class_Node__opt a) (returned: bool).
    handle_or_closed owner snapshot h t x p returned ** pure (returned /\ snapshot == expected)
  ensures S.class_SortedSet__inv owner #p expected

ghost fn continuing_handle_window (#a: Type0) (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: R.handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) (returned: bool)
  requires handle_or_closed owner snapshot h t x p returned ** pure (~returned)
  ensures R.handle_window h t x p
