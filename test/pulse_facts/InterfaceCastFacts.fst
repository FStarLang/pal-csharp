module InterfaceCastFacts
#lang-pulse

open Pulse
module D = FStar.Dyn
module B = Pulse.Lib.Box
module A = Pulse.Lib.CSharp.Assumptions

#set-options "--z3rlimit 10"

// A target-relative partition, not a registry of all concrete implementation types.
// `b` can package arbitrary non-matching implementations. Establishing that partition
// from CLR type information is a separate obligation of a concrete adapter.
noeq type payload (a b: Type0) =
  | Matches : value:a -> payload a b
  | Misses : value:b -> payload a b

let cast_value (#a #b: Type0) (w: payload a b) : option a =
  match w with
  | Matches x -> Some x
  | Misses _ -> None

let resource (#a #b #s: Type0)
    (owns_a: a -> perm -> s -> slprop)
    (owns_b: b -> perm -> s -> slprop)
    (w: payload a b) (p: perm) (m: s) : slprop =
  match w with
  | Matches x -> owns_a x p m
  | Misses x -> owns_b x p m

let interface_at (#a #b #s: Type0)
    (owns_a: a -> perm -> s -> slprop)
    (owns_b: b -> perm -> s -> slprop)
    (o: D.dyn) (w: erased (payload a b)) (p: perm) (m: erased s) : slprop =
  pure (o == D.mkdyn (reveal w)) ** resource owns_a owns_b w p m

fn try_cast (#a #b #s: Type0)
    (owns_a: a -> perm -> s -> slprop)
    (owns_b: b -> perm -> s -> slprop)
    (o: D.dyn) (#w: erased (payload a b)) (#p: perm) (#m: erased s)
  preserves interface_at owns_a owns_b o w p m
  returns result: option a
  ensures pure (result == cast_value w)
{
  unfold (interface_at owns_a owns_b o w p m);
  let actual = A.recover #(payload a b) #w o;
  let result = cast_value actual;
  fold (interface_at owns_a owns_b o w p m);
  result
}

ghost
fn open_match (#a #b #s: Type0)
    (owns_a: a -> perm -> s -> slprop)
    (owns_b: b -> perm -> s -> slprop)
    (o: D.dyn) (x: a)
    (#w: erased (payload a b) { cast_value w == Some x })
    (#p: perm) (#m: erased s)
  requires interface_at owns_a owns_b o w p m
  ensures owns_a x p m ** pure (o == D.mkdyn (reveal w))
{
  assert pure (reveal w == Matches x);
  unfold (interface_at owns_a owns_b o w p m);
  rewrite (resource owns_a owns_b w p m) as (resource owns_a owns_b (Matches x) p m);
  unfold (resource owns_a owns_b (Matches x) p m);
}

ghost
fn close_match (#a #b #s: Type0)
    (owns_a: a -> perm -> s -> slprop)
    (owns_b: b -> perm -> s -> slprop)
    (o: D.dyn) (x: a)
    (#w: erased (payload a b) { cast_value w == Some x /\ o == D.mkdyn (reveal w) })
    (#p: perm) (#m: erased s)
  requires owns_a x p m
  ensures interface_at owns_a owns_b o w p m
{
  assert pure (reveal w == Matches x);
  fold (resource owns_a owns_b (Matches x) p m);
  rewrite (resource owns_a owns_b (Matches x) p m) as (resource owns_a owns_b w p m);
  fold (interface_at owns_a owns_b o w p m);
}

let cell_owns (x: B.box int) (p: perm) (m: int) : slprop = B.pts_to x #p m

// The alternative implementation has a distinct concrete representation.
noeq type pair_cell = { first: B.box int; second: B.box int }

let pair_owns (x: pair_cell) (p: perm) (m: int) : slprop =
  exists* left right. B.pts_to x.first #p left ** B.pts_to x.second #p right **
  pure (left + right == m)

fn matching_client (x: B.box int) (#p: perm) (#m: erased int)
  preserves cell_owns x p m
  returns result: int
  ensures pure (result == reveal m)
{
  let w = Matches #(B.box int) #pair_cell x;
  let o = D.mkdyn w;
  fold (resource cell_owns pair_owns (Matches x) p m);
  rewrite (resource cell_owns pair_owns (Matches x) p m) as (resource cell_owns pair_owns w p m);
  fold (interface_at cell_owns pair_owns o (hide w) p m);
  let cast = try_cast cell_owns pair_owns o;
  match cast {
    None -> { unreachable (); }
    Some y -> {
      assert pure (y == x);
      open_match cell_owns pair_owns o y;
      unfold (cell_owns y p m);
      let result = B.op_Bang y;
      fold (cell_owns y p m);
      close_match cell_owns pair_owns o y #(hide w) #p #m;
      let second = try_cast cell_owns pair_owns o;
      assert pure (second == Some x);
      open_match cell_owns pair_owns o x;
      result
    }
  }
}

fn nonmatching_client (x: pair_cell) (#p: perm) (#m: erased int)
  preserves pair_owns x p m
  returns result: option (B.box int)
  ensures pure (result == None)
{
  let w = Misses #(B.box int) #pair_cell x;
  let o = D.mkdyn w;
  fold (resource cell_owns pair_owns (Misses x) p m);
  rewrite (resource cell_owns pair_owns (Misses x) p m) as (resource cell_owns pair_owns w p m);
  fold (interface_at cell_owns pair_owns o (hide w) p m);
  let cast = try_cast cell_owns pair_owns o;
  unfold (interface_at cell_owns pair_owns o (hide w) p m);
  rewrite (resource cell_owns pair_owns w p m) as (resource cell_owns pair_owns (Misses x) p m);
  unfold (resource cell_owns pair_owns (Misses x) p m);
  cast
}

[@@expect_failure]
ghost
fn cast_cannot_duplicate_ownership (x: B.box int) (#m: erased int)
  requires cell_owns x 1.0R m
  ensures cell_owns x 1.0R m ** cell_owns x 1.0R m
{
  let w = Matches #(B.box int) #pair_cell x;
  let o = D.mkdyn w;
  fold (resource cell_owns pair_owns (Matches x) 1.0R m);
  rewrite (resource cell_owns pair_owns (Matches x) 1.0R m) as (resource cell_owns pair_owns w 1.0R m);
  fold (interface_at cell_owns pair_owns o (hide w) 1.0R m);
  open_match cell_owns pair_owns o x;
}

// A single descriptor, unlike the target-relative prototype above, gives every
// cast a consistent answer. Its code universe is a parameter, not a closed list.
noeq type tagged (code: eqtype) (rep: code -> Type0) = {
  tag: code;
  value: rep tag;
}

let project (#code: eqtype) (#rep: code -> Type0)
    (target: code) (w: tagged code rep) : option (rep target) =
  if w.tag = target then Some w.value else None

let tagged_at (#code: eqtype) (#rep: code -> Type0) (#s: Type0)
    (owns: (tag: code) -> rep tag -> perm -> s -> slprop)
    (o: D.dyn) (w: erased (tagged code rep)) (p: perm) (m: erased s) : slprop =
  pure (o == D.mkdyn (reveal w)) ** owns (reveal w).tag (reveal w).value p m

fn checked_cast (#code: eqtype) (#rep: code -> Type0) (#s: Type0)
    (owns: (tag: code) -> rep tag -> perm -> s -> slprop)
    (target: code) (o: D.dyn)
    (#w: erased (tagged code rep)) (#p: perm) (#m: erased s)
  preserves tagged_at owns o w p m
  returns result: option (rep target)
  ensures pure (result == project target w /\
                (Some? result <==> (reveal w).tag == target))
{
  unfold (tagged_at owns o w p m);
  let actual = A.recover #(tagged code rep) #w o;
  let result = project target actual;
  fold (tagged_at owns o w p m);
  result
}

ghost
fn open_tagged (#code: eqtype) (#rep: code -> Type0) (#s: Type0)
    (owns: (tag: code) -> rep tag -> perm -> s -> slprop)
    (target: code) (o: D.dyn) (x: rep target)
    (#w: erased (tagged code rep) { project target w == Some x })
    (#p: perm) (#m: erased s)
  requires tagged_at owns o w p m
  ensures owns target x p m ** pure (o == D.mkdyn (reveal w))
{
  assert pure ((reveal w).tag == target);
  assert pure ((reveal w).value == x);
  unfold (tagged_at owns o w p m);
  rewrite (owns (reveal w).tag (reveal w).value p m) as (owns target x p m);
}

ghost
fn close_tagged (#code: eqtype) (#rep: code -> Type0) (#s: Type0)
    (owns: (tag: code) -> rep tag -> perm -> s -> slprop)
    (target: code) (o: D.dyn) (x: rep target)
    (#w: erased (tagged code rep) {
      project target w == Some x /\ o == D.mkdyn (reveal w) })
    (#p: perm) (#m: erased s)
  requires owns target x p m
  ensures tagged_at owns o w p m
{
  assert pure ((reveal w).tag == target);
  assert pure ((reveal w).value == x);
  rewrite (owns target x p m) as (owns (reveal w).tag (reveal w).value p m);
  fold (tagged_at owns o w p m);
}

let same_rep (_: nat) : Type0 = B.box int
let owns_code (_: nat) (x: B.box int) (p: perm) (m: int) : slprop =
  B.pts_to x #p m

// Distinct source classes may have the same F* representation. A representation
// test alone would be wrong; the runtime code, not `B.box int`, decides the cast.
fn distinct_tags_same_rep (x: B.box int) (#p: perm) (#m: erased int)
  preserves B.pts_to x #p m
  returns result: int
  ensures pure (result == reveal m)
{
  let w: tagged nat same_rep = { tag = 1; value = x };
  let o = D.mkdyn w;
  fold (owns_code 1 x p m);
  rewrite (owns_code 1 x p m) as (owns_code w.tag w.value p m);
  fold (tagged_at owns_code o (hide w) p m);
  let miss = checked_cast owns_code 0 o;
  assert pure (miss == None);
  let hit = checked_cast owns_code 1 o;
  match hit {
    None -> { unreachable (); }
    Some y -> {
      assert pure (y == x);
      open_tagged owns_code 1 o y;
      unfold (owns_code 1 y p m);
      let result = B.op_Bang y;
      fold (owns_code 1 y p m);
      close_tagged owns_code 1 o y #(hide w) #p #m;
      let miss_again = checked_cast owns_code 0 o;
      assert pure (miss_again == None);
      open_tagged owns_code 1 o x;
      unfold (owns_code 1 x p m);
      result
    }
  }

}

[@@expect_failure]
ghost
fn cannot_change_runtime_tag (o: D.dyn) (x: B.box int) (#m: erased int)
  requires tagged_at owns_code o (hide ({ tag = 1; value = x })) 1.0R m
  ensures tagged_at owns_code o (hide ({ tag = 0; value = x })) 1.0R m
{
  unfold (tagged_at owns_code o (hide ({ tag = 1; value = x })) 1.0R m);
  fold (tagged_at owns_code o (hide ({ tag = 0; value = x })) 1.0R m);
}

// A contents-only classification cannot distinguish two source classes having
// exactly the same contents. This is the information lost by the current
// enumerable snapshot conversion, before ownership recovery is even considered.
let contents_do_not_determine_type (#t: Type0)
    (classify: FStar.Seq.seq t -> bool) (contents: FStar.Seq.seq t)
  : Lemma (not (classify contents == true /\ classify contents == false))
  = ()

fn concrete_clients ()
  requires emp
  returns result: bool
  ensures emp ** pure result
{
  let x = B.alloc 7;
  fold (cell_owns x 1.0R 7);
  let first = matching_client x;
  unfold (cell_owns x 1.0R 7);
  let second = distinct_tags_same_rep x;
  let left = B.alloc 3;
  let right = B.alloc 4;
  let pair = { first = left; second = right };
  rewrite (B.pts_to left 3) as (B.pts_to pair.first 3);
  rewrite (B.pts_to right 4) as (B.pts_to pair.second 4);
  fold (pair_owns pair 1.0R 7);
  let miss = nonmatching_client pair;
  unfold (pair_owns pair 1.0R 7);
  with l r. assert (B.pts_to pair.first l ** B.pts_to pair.second r);
  rewrite (B.pts_to pair.first l) as (B.pts_to left l);
  rewrite (B.pts_to pair.second r) as (B.pts_to right r);
  B.free left;
  B.free right;
  B.free x;
  first = 7 && second = 7 && None? miss
}
