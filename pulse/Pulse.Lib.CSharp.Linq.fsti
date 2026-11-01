module Pulse.Lib.CSharp.Linq
#lang-pulse

/// `Enumerable.OrderBy(key).ToList()` (doc/translation.md §20).
///
/// MODELING AXIOM. `Enumerable.OrderBy` is documented to perform a *stable* sort, using
/// `Comparer<TKey>.Default` to compare keys. A stable sort under a total preorder is a
/// function of its input -- there is exactly one sorted permutation that keeps equal
/// keys in input order -- so `sort_by` below, a stable insertion sort, *is* what LINQ
/// computes, whatever algorithm LINQ uses to compute it. `ToList` materialises the
/// result into a fresh list that nothing else references.
///
/// The key selector must be pure and total (the translator admits only a lambda whose
/// body is a specification expression of its parameter), so that LINQ calling it any
/// number of times, in any order, is unobservable.

open Pulse
open Pulse.Lib.CSharp.Array
module A = Pulse.Lib.Array
module Seq = FStar.Seq

let rec insert (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (x: t) (s: Seq.seq t)
  : Tot (Seq.seq t) (decreases Seq.length s)
  = if Seq.length s = 0 then Seq.create 1 x
    else if le (key x) (key (Seq.head s)) then Seq.cons x s
    else Seq.cons (Seq.head s) (insert key le x (Seq.tail s))

/// The stable sort: each element is inserted *before* every later element with an
/// equal key, so equal keys keep their input order.
let rec sort_by (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (s: Seq.seq t)
  : Tot (Seq.seq t) (decreases Seq.length s)
  = if Seq.length s = 0 then Seq.empty
    else insert key le (Seq.head s) (sort_by key le (Seq.tail s))

val sort_by_length (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (s: Seq.seq t)
  : Lemma (Seq.length (sort_by key le s) == Seq.length s)
          [SMTPat (Seq.length (sort_by key le s))]

/// `sort_by` permutes: it neither drops nor duplicates an element.
val sort_by_count (#t: eqtype) (#k: Type) (key: t -> k) (le: k -> k -> bool) (s: Seq.seq t) (x: t)
  : Lemma (Seq.count x (sort_by key le s) == Seq.count x s)
          [SMTPat (Seq.count x (sort_by key le s))]

/// Hence every property of all the elements survives sorting.
val sort_by_forall (#t: eqtype) (#k: Type) (key: t -> k) (le: k -> k -> bool) (s: Seq.seq t)
                   (p: t -> bool)
  : Lemma ((forall (i: nat { i < Seq.length s }). p (Seq.index s i)) <==>
           (forall (i: nat { i < Seq.length (sort_by key le s) }). p (Seq.index (sort_by key le s) i)))

let total_preorder (#k: Type) (le: k -> k -> bool) : prop =
  (forall a b. le a b \/ le b a) /\ (forall a b c. le a b /\ le b c ==> le a c)

let sorted (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (s: Seq.seq t) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> le (key (Seq.index s i)) (key (Seq.index s j))

val sort_by_sorted (#t: eqtype) (#k: Type) (key: t -> k) (le: k -> k -> bool) (s: Seq.seq t)
  : Lemma (requires total_preorder le) (ensures sorted key le (sort_by key le s))

/// `source.OrderBy(key).ToList()`.
fn order_by_to_list (#t #k: Type0) (a: array t) (key: t -> k) (le: k -> k -> bool)
                    (#p: perm) (#s: Ghost.erased (Seq.seq t))
  preserves A.pts_to a #p s
  returns  r : array t
  ensures  A.pts_to r (sort_by key le s)
