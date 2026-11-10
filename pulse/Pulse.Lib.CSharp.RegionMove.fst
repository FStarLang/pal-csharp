module Pulse.Lib.CSharp.RegionMove
#lang-pulse

/// R27.44. Two regions of one class open in one method: one owner's region set aside
/// (`parked`) while another owner's is used, and a freshly built tree moved from one
/// region into the other (`move`). Every cell stays where it was in memory; what moves is
/// the ownership of the cells the tree is built of.
///
/// Nothing here is trusted: it is built on `Pulse.Lib.CSharp.Region`, whose only trusted
/// fact is `RefEq.ref_eq` (R27.8).

open Pulse.Lib.Pervasives
open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree

(* ------------------------------------------------------------------------------------ *)
(* Parking                                                                               *)

/// A region set aside: the same cells, under a name a region call cannot pick up.
let parked (#a: Type0) (#p: perm) (h: heap a) : slprop =
  exists* (u: bool). pure (u == true) ** region #a #p h

ghost fn park (#a: Type0) (#p: perm) (h: heap a)
  requires region #a #p h
  ensures  parked #a #p h
{
  fold (parked #a #p h)
}

ghost fn unpark (#a: Type0) (#p: perm) (h: heap a)
  requires parked #a #p h
  ensures  region #a #p h
{
  unfold (parked #a #p h)
}

(* ------------------------------------------------------------------------------------ *)
(* Splitting a heap by a set of boxes                                                   *)

let rec inb (#a: Type0) (s: list (B.box a)) (x: B.box a) : Tot bool (decreases s) =
  match s with
  | [] -> false
  | y :: t -> eq_box y x || inb t x

let rec inb_memP (#a: Type0) (s: list (B.box a)) (x: B.box a)
  : Lemma (ensures inb s x <==> L.memP x s) (decreases s) [SMTPat (inb s x)]
  = match s with
    | [] -> ()
    | _ :: t -> inb_memP t x

/// The cells of `h` whose box is in `s`, and the others.
let rec keep (#a: Type0) (s: list (B.box a)) (h: heap a) : Tot (heap a) (decreases h) =
  match h with
  | [] -> []
  | (b, v) :: t -> if inb s b then (b, v) :: keep s t else keep s t

let rec drop (#a: Type0) (s: list (B.box a)) (h: heap a) : Tot (heap a) (decreases h) =
  match h with
  | [] -> []
  | (b, v) :: t -> if inb s b then drop s t else (b, v) :: drop s t

let rec lookup_keep (#a: Type0) (s: list (B.box a)) (h: heap a) (y: B.box a)
  : Lemma (ensures lookup (keep s h) y == (if inb s y then lookup h y else None)) (decreases h)
          [SMTPat (lookup (keep s h) y)]
  = match h with
    | [] -> ()
    | (b, _) :: t -> lookup_keep s t y

let rec lookup_drop (#a: Type0) (s: list (B.box a)) (h: heap a) (y: B.box a)
  : Lemma (ensures lookup (drop s h) y == (if inb s y then None else lookup h y)) (decreases h)
          [SMTPat (lookup (drop s h) y)]
  = match h with
    | [] -> ()
    | (b, _) :: t -> lookup_drop s t y

let rec lookup_append (#a: Type0) (h1 h2: heap a) (y: B.box a)
  : Lemma (ensures lookup (h1 `L.append` h2) y == (match lookup h1 y with Some v -> Some v | None -> lookup h2 y))
          (decreases h1)
          [SMTPat (lookup (h1 `L.append` h2) y)]
  = match h1 with
    | [] -> ()
    | _ :: t -> lookup_append t h2 y

ghost fn rec split (#a: Type0) (#p: perm) (s: list (B.box a)) (h: heap a)
  requires cells p h
  ensures  cells p (keep s h) ** cells p (drop s h)
  decreases h
{
  match h {
    Nil -> {
      rewrite (cells p h) as (cells p (keep s h));
      fold (cells p ([] <: heap a));
      rewrite (cells p ([] <: heap a)) as (cells p (drop s h));
    }
    Cons hd t -> {
      let b = fst hd;
      let w = snd hd;
      rewrite (cells p h) as (B.pts_to b #p w ** cells p t);
      split s t;
      if (inb s b) {
        fold (cells p ((b, w) :: keep s t));
        rewrite (cells p ((b, w) :: keep s t)) as (cells p (keep s h));
        rewrite (cells p (drop s t)) as (cells p (drop s h));
      } else {
        fold (cells p ((b, w) :: drop s t));
        rewrite (cells p ((b, w) :: drop s t)) as (cells p (drop s h));
        rewrite (cells p (keep s t)) as (cells p (keep s h));
      }
    }
  }
}

ghost fn rec join (#a: Type0) (#p: perm) (h1 h2: heap a)
  requires cells p h1 ** cells p h2
  ensures  cells p (h1 `L.append` h2)
  decreases h1
{
  match h1 {
    Nil -> {
      rewrite (cells p h1) as emp;
      rewrite (cells p h2) as (cells p (h1 `L.append` h2));
    }
    Cons hd t -> {
      let b = fst hd;
      let w = snd hd;
      rewrite (cells p h1) as (B.pts_to b #p w ** cells p t);
      join t h2;
      fold (cells p ((b, w) :: (t `L.append` h2)));
      rewrite (cells p ((b, w) :: (t `L.append` h2))) as (cells p (h1 `L.append` h2));
    }
  }
}

/// Two regions held whole own no box in common.
ghost fn rec apart (#a: Type0) (h1 h2: heap a)
  preserves cells 1.0R h1 ** cells 1.0R h2
  ensures  pure (forall (y: B.box a). mem h1 y ==> ~ (mem h2 y))
  decreases h1
{
  match h1 {
    Nil -> { () }
    Cons hd t -> {
      let b = fst hd;
      let w = snd hd;
      rewrite (cells 1.0R h1) as (B.pts_to b #1.0R w ** cells 1.0R t);
      apart t h2;
      fresh h2 b;
      fold (cells 1.0R ((b, w) :: t));
      rewrite (cells 1.0R ((b, w) :: t)) as (cells 1.0R h1);
    }
  }
}

(* ------------------------------------------------------------------------------------ *)
(* Moving a fresh tree                                                                   *)

/// What `x` reaches in `h`, as a set of boxes: `boxes (ltree ..)`, computed (not ghost),
/// so that a heap split by it can index a resource.
let rec reach_n (#a: Type0) (left right: a -> B.box a) (n: nat) (h: heap a) (x: B.box a)
  : Tot (list (B.box a)) (decreases n)
  = if n = 0 || B.is_null x then []
    else match lookup h x with
      | None -> []
      | Some r -> x :: L.append (reach_n left right (n - 1) h (left r))
                                (reach_n left right (n - 1) h (right r))

let rec reach_n_boxes (#a: Type0) (left right: a -> B.box a) (n: nat) (h: heap a) (x: B.box a)
  : Lemma (ensures reach_n left right n h x == boxes (ltree_n left right n h x)) (decreases n)
  = if n = 0 || B.is_null x then ()
    else match lookup h x with
      | None -> ()
      | Some r -> reach_n_boxes left right (n - 1) h (left r);
                 reach_n_boxes left right (n - 1) h (right r)

let reach (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a) : list (B.box a) =
  reach_n left right (fuel h) h x

let reach_boxes (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (ensures reach left right h x == boxes (ltree left right h x))
          [SMTPat (reach left right h x)]
  = reveal_opaque (`%ltree) (ltree #a); reach_n_boxes left right (fuel h) h x

/// The region `x`'s tree leaves, and the one it joins.
let moved_from (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a) : heap a =
  drop (reach left right h x) h

let moved_into (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a) (into: heap a)
  : heap a =
  keep (reach left right h x) h `L.append` into

/// A tree whose every lookup is the same in `h1` is the same tree there.
let rec realizes_agree (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (y: B.box a)
    (t: T.tree (B.box a & a))
  : Lemma (requires realizes left right h0 y t /\
                    (forall (z: B.box a). L.memP z (boxes t) ==> lookup h1 z == lookup h0 z))
          (ensures realizes left right h1 y t)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (_, r) rr ->
      realizes_agree left right h0 h1 (left r) l;
      realizes_agree left right h0 h1 (right r) rr

let agree_tree (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (y: B.box a)
  : Lemma (requires unshared left right h0 y /\
                    (forall (z: B.box a). L.memP z (reach left right h0 y) ==> lookup h1 z == lookup h0 z))
          (ensures unshared left right h1 y /\ ltree left right h1 y == ltree left right h0 y)
  = unshared_elim left right h0 y;
    realizes_agree left right h0 h1 y (ltree left right h0 y);
    unshared_intro left right h1 y (ltree left right h0 y)

let reach_mem (#a: Type0) (left right: a -> B.box a) (h: heap a) (y z: B.box a)
  : Lemma (requires unshared left right h y /\ L.memP z (reach left right h y)) (ensures mem h z)
  = unshared_elim left right h y;
    realizes_mem left right h y (ltree left right h y) z

/// What the source region keeps: every tree of the heap before the call is as it was.
let stays (#a: Type0) (left right: a -> B.box a) (h0 h1: heap a) (x y: B.box a)
  : Lemma (requires unshared left right h0 y /\ unshared left right h1 x /\
                    reshaped left right h0 h1 B.null x)
          (ensures unshared left right (moved_from left right h1 x) y /\
                   ltree left right (moved_from left right h1 x) y == ltree left right h0 y)
  = let s = reach left right h1 x in
    let aux (z: B.box a)
      : Lemma (L.memP z (reach left right h0 y) ==> lookup (moved_from left right h1 x) z == lookup h0 z)
      = if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (reach left right h0 y))
        then reach_mem left right h0 y z else () in
    FStar.Classical.forall_intro aux;
    agree_tree left right h0 (moved_from left right h1 x) y

/// What the target region had: every tree of it is as it was.
let kept (#a: Type0) (left right: a -> B.box a) (h1 into: heap a) (x y: B.box a)
  : Lemma (requires unshared left right into y /\
                    (forall (z: B.box a). mem h1 z ==> ~ (mem into z)))
          (ensures unshared left right (moved_into left right h1 x into) y /\
                   ltree left right (moved_into left right h1 x into) y == ltree left right into y)
  = let aux (z: B.box a)
      : Lemma (L.memP z (reach left right into y) ==>
               lookup (moved_into left right h1 x into) z == lookup into z)
      = if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (reach left right into y))
        then begin
          reach_mem left right into y z;
          if inb (reach left right h1 x) z then () else ()
        end else () in
    FStar.Classical.forall_intro aux;
    agree_tree left right into (moved_into left right h1 x into) y

/// The moved tree is the same tree in its new region.
let arrives (#a: Type0) (left right: a -> B.box a) (h1 into: heap a) (x: B.box a)
  : Lemma (requires unshared left right h1 x)
          (ensures unshared left right (moved_into left right h1 x into) x /\
                   ltree left right (moved_into left right h1 x into) x == ltree left right h1 x)
  = let aux (z: B.box a)
      : Lemma (L.memP z (reach left right h1 x) ==>
               lookup (moved_into left right h1 x into) z == lookup h1 z)
      = if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (reach left right h1 x))
        then reach_mem left right h1 x z else () in
    FStar.Classical.forall_intro aux;
    agree_tree left right h1 (moved_into left right h1 x into) x

/// R27.44. A tree a call built fresh in one region (`reshaped h0 h1 null x`: nothing the
/// region held before is touched, and every box of the tree is new) moves into another:
/// what the source held before the call is as it was, what the target held is as it was,
/// and the target now holds the tree.
ghost fn move (#a: Type0) (left right: a -> B.box a) (h0: erased (heap a)) (h1 into: heap a)
    (x: B.box a)
  requires region #a #1.0R h1 ** region #a #1.0R into **
           pure (unshared left right h1 x /\ reshaped left right h0 h1 B.null x)
  ensures  region #a #1.0R (moved_from left right h1 x) **
           region #a #1.0R (moved_into left right h1 x into) **
           pure (unshared left right (moved_into left right h1 x into) x /\
                 ltree left right (moved_into left right h1 x into) x == ltree left right h1 x /\
                 (forall (y: B.box a). {:pattern unshared left right (moved_from left right h1 x) y \/
                                                 ltree left right (moved_from left right h1 x) y}
                    unshared left right h0 y ==>
                    unshared left right (moved_from left right h1 x) y /\
                    ltree left right (moved_from left right h1 x) y == ltree left right h0 y) /\
                 (forall (y: B.box a). {:pattern unshared left right (moved_into left right h1 x into) y \/
                                                 ltree left right (moved_into left right h1 x into) y}
                    unshared left right into y ==>
                    unshared left right (moved_into left right h1 x into) y /\
                    ltree left right (moved_into left right h1 x into) y == ltree left right into y))
{
  unfold (region #a #1.0R h1);
  unfold (region #a #1.0R into);
  apart h1 into;
  arrives left right h1 into x;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (stays left right h0 h1 x));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (kept left right h1 into x));
  split (reach left right h1 x) h1;
  join (keep (reach left right h1 x) h1) into;
  rewrite (cells 1.0R (drop (reach left right h1 x) h1))
       as (cells 1.0R (moved_from left right h1 x));
  rewrite (cells 1.0R (keep (reach left right h1 x) h1 `L.append` into))
       as (cells 1.0R (moved_into left right h1 x into));
  fold (region #a #1.0R (moved_from left right h1 x));
  fold (region #a #1.0R (moved_into left right h1 x into));
}

/// R27.55. The whole tree of an owner that is being discarded joins another region: the
/// target holds the tree, and every tree it held is as it was. Unlike `move`, nothing is
/// said of what the source keeps, since its owner is not closed again.
ghost fn adopt (#a: Type0) (left right: a -> B.box a) (h1 into: heap a) (x: B.box a)
  requires region #a #1.0R h1 ** region #a #1.0R into **
           pure (unshared left right h1 x)
  ensures  region #a #1.0R (moved_from left right h1 x) **
           region #a #1.0R (moved_into left right h1 x into) **
           pure (unshared left right (moved_into left right h1 x into) x /\
                 ltree left right (moved_into left right h1 x into) x == ltree left right h1 x /\
                 (forall (y: B.box a). {:pattern unshared left right (moved_into left right h1 x into) y \/
                                                 ltree left right (moved_into left right h1 x into) y}
                    unshared left right into y ==>
                    unshared left right (moved_into left right h1 x into) y /\
                    ltree left right (moved_into left right h1 x into) y == ltree left right into y))
{
  unfold (region #a #1.0R h1);
  unfold (region #a #1.0R into);
  apart h1 into;
  arrives left right h1 into x;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (kept left right h1 into x));
  split (reach left right h1 x) h1;
  join (keep (reach left right h1 x) h1) into;
  rewrite (cells 1.0R (drop (reach left right h1 x) h1))
       as (cells 1.0R (moved_from left right h1 x));
  rewrite (cells 1.0R (keep (reach left right h1 x) h1 `L.append` into))
       as (cells 1.0R (moved_into left right h1 x into));
  fold (region #a #1.0R (moved_from left right h1 x));
  fold (region #a #1.0R (moved_into left right h1 x into));
}
