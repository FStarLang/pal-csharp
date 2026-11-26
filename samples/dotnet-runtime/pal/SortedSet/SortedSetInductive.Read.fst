module SortedSetInductive.Read
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Cursor
module S = Class_SortedSet
module M = Struct_SortedSetModel
module N = Class_Node
module B = Pulse.Lib.Box
module EQ = Pulse.Lib.CSharp.EqualityModel

#set-options "--z3rlimit 10"

let view_root (#a: Type0) (t: O.tree a) (c: Pulse.Lib.CSharp.Order.comparer a)
    (root: N.class_Node__opt a) (level: int) (lo hi: a) (la ua: bool) =
  (root == B.null \/ O.member t root) /\
  O.lookup t root == Pulse.Lib.CSharp.SearchTree.range_root c (O.values t) lo hi la ua /\
  0 <= level /\
  (root == B.null \/ level == SortedSetCount.range_depth c (O.values t) lo hi la ua)

unfold let owner_lease (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (t: O.tree a) (p: perm) =
  O.owns t p ** (O.owns t p @==> O.owner root s p)

// Each lease is confined to one operation. Its trade restores exactly the
// original predicate, snapshot, and permission, not merely an equivalent set.
ghost fn begin_owner (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (t: O.tree a) (p: perm)
  requires O.owner root s p ** pure (t == O.active s)
  ensures owner_lease root s t p
{
  unfold (O.owner root s p);
  rewrite (O.owns (O.active s) p) as (O.owns t p);
  intro (O.owns t p @==> O.owner root s p)
    #(O.retained (O.retired_state s) p) fn _ {
      rewrite (O.owns t p) as (O.owns (O.active s) p);
      fold (O.owner root s p);
    };
}

[@@pulse_intro]
ghost fn end_owner (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (p: perm)
  requires exists* (t: O.tree a).
    (O.owns t p @==> O.owner root s p) ** O.owns t p
  ensures O.owner root s p
{
  Pulse.Lib.Trade.Util.elim _ _;
}

// Collection handles retain their receiver's equality evidence. The tree-only
// leases above deliberately do not acquire an equality constraint.
unfold let inv (#a: Type0) {| equality_a: EQ.has_equality a |} (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (p: perm) =
  S.class_SortedSet__inv set #p m

let labels (#a: Type0) {| equality_a: EQ.has_equality a |} (m: S.class_SortedSet__model a) = m.M.fld_Labels

type handle (a: Type0) {| equality_a: EQ.has_equality a |} = S.class_SortedSet a & S.class_SortedSet__model a

let snapshot_of (#a: Type0) {| equality_a: EQ.has_equality a |} (m: S.class_SortedSet__model a)
  : r:S.class_SortedSet__model a{r == m} = m

let handle_of_view (#a: Type0) {| equality_a: EQ.has_equality a |} (view: Struct_SortedSet_TreeSubSet.struct_SortedSet_TreeSubSet a)
    (snapshot: S.class_SortedSet__model a) : handle a =
  view.Struct_SortedSet_TreeSubSet.fld__underlying, snapshot

let handle_of_view_facts (#a: Type0) {| equality_a: EQ.has_equality a |} (view: Struct_SortedSet_TreeSubSet.struct_SortedSet_TreeSubSet a)
    (snapshot: S.class_SortedSet__model a)
  : Lemma (fst (handle_of_view view snapshot) == view.Struct_SortedSet_TreeSubSet.fld__underlying /\
           snd (handle_of_view view snapshot) == snapshot) = ()

let handle_matches_view (#a: Type0) {| equality_a: EQ.has_equality a |} (h: handle a)
    (view: Struct_SortedSet_TreeSubSet.struct_SortedSet_TreeSubSet a)
    (snapshot: S.class_SortedSet__model a) : prop =
  fst h == view.Struct_SortedSet_TreeSubSet.fld__underlying /\ snd h == snapshot

unfold let handle_window (#a: Type0) {| equality_a: EQ.has_equality a |} (h: handle a) (t: O.tree a)
    (x: N.class_Node__opt a) (p: perm) =
  C.window t x p ** (O.owns t p @==> inv (fst h) (snd h) p)

let handle_matches (#a: Type0) {| equality_a: EQ.has_equality a |} (h: handle a) (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) : prop =
  fst h == owner /\ snd h == snapshot

unfold let set_window (#a: Type0) {| equality_a: EQ.has_equality a |} (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (t: O.tree a) (x: N.class_Node__opt a) (p: perm) =
  C.window t x p ** (O.owns t p @==> inv owner snapshot p)

ghost fn window_to_handle (#a: Type0) {| equality_a: EQ.has_equality a |} (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: handle a) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires set_window owner snapshot t x p ** pure (handle_matches h owner snapshot)
  ensures handle_window h t x p
{
  rewrite (set_window owner snapshot t x p) as (handle_window h t x p);
}

ghost fn window_from_handle (#a: Type0) {| equality_a: EQ.has_equality a |} (owner: S.class_SortedSet a)
    (snapshot: S.class_SortedSet__model a) (h: handle a) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires handle_window h t x p ** pure (handle_matches h owner snapshot)
  ensures set_window owner snapshot t x p
{
  rewrite (handle_window h t x p) as (set_window owner snapshot t x p);
}

unfold let set_lease (#a: Type0) {| equality_a: EQ.has_equality a |} (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (t: O.tree a) (p: perm) =
  O.owns t p ** (O.owns t p @==> inv set m p)

ghost fn begin_set (#a: Type0) {| equality_a: EQ.has_equality a |} (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (t: O.tree a) (p: perm)
  requires inv set m p ** pure (t == m.M.fld_Labels)
  ensures set_lease set m t p
{
  unfold (inv set m p);
  unfold (S.class_SortedSet__inv set #p m);
  with r. _;
  unfold (O.owner r.S.fld_root r.S.fld_ownershipState p);
  rewrite (O.owns (O.active r.S.fld_ownershipState) p) as (O.owns t p);
  intro (O.owns t p @==> inv set m p)
    #(B.pts_to set #p r ** O.retained (O.retired_state r.S.fld_ownershipState) p)
    fn _ {
      rewrite (O.owns t p) as (O.owns (O.active r.S.fld_ownershipState) p);
      fold (O.owner r.S.fld_root r.S.fld_ownershipState p);
      fold (S.class_SortedSet__inv set #p m);
      fold (inv set m p);
    };
}

// Introduction rules infer evidence from the matched resource, rather than
// running typeclass search before the element type has been determined.
[@@pulse_intro]
ghost fn end_set (#a: Type0) (#equality_a: EQ.has_equality a) (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (p: perm)
  requires exists* (t: O.tree a).
    (O.owns t p @==> inv set m p) ** O.owns t p
  ensures S.class_SortedSet__inv set #p m
{
  Pulse.Lib.Trade.Util.elim _ _;
  unfold (inv set m p);
}

// Restore an owner directly from its current cursor and the already-established
// restoration trade. Unlike a generic `owns` introduction rule, this cannot
// recursively try to manufacture the cursor's child-tree ownership.
[@@pulse_intro]
ghost fn end_set_window (#a: Type0) (#equality_a: EQ.has_equality a) (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (p: perm)
  requires exists* (t: O.tree a) (x: N.class_Node__opt a).
    (O.owns t p @==> inv set m p) ** C.window t x p
  ensures S.class_SortedSet__inv set #p m
{
  with t x. assert (C.window t x p ** (O.owns t p @==> inv set m p));
  C.close_node t x p;
  Pulse.Lib.Trade.Util.elim _ _;
  unfold (inv set m p);
}

// The caller can have exposed the cursor already to read a field. Check that
// owner restoration still follows from those ordinary resources alone.
ghost fn end_set_window_unfolded (#a: Type0) {| equality_a: EQ.has_equality a |} (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires C.window t x p ** (O.owns t p @==> inv set m p)
  ensures S.class_SortedSet__inv set #p m
{
  unfold (C.window t x p);
}

unfold let any_window (#a: Type0) (t: O.tree a) (p: perm) =
  exists* (x: N.class_Node__opt a). C.window t x p

ghost fn close_window (#a: Type0) (t: O.tree a) (p: perm)
  requires any_window t p
  ensures O.owns t p
{
  unfold (any_window t p);
  with x. _;
  C.close_node t x p;
}
