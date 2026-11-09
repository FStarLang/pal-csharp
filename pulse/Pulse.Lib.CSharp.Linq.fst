module Pulse.Lib.CSharp.Linq
#lang-pulse

open Pulse
open Pulse.Lib.CSharp.Array
module A = Pulse.Lib.CSharp.Array
module Seq = FStar.Seq
module SP = FStar.Seq.Properties

let rec insert_length (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (x: t) (s: Seq.seq t)
  : Lemma (ensures Seq.length (insert key le x s) == Seq.length s + 1)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if le (key x) (key (Seq.head s)) then ()
    else insert_length key le x (Seq.tail s)

let rec sort_by_length #t #k key le s
  : Lemma (ensures Seq.length (sort_by key le s) == Seq.length s) (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (sort_by_length key le (Seq.tail s);
          insert_length key le (Seq.head s) (sort_by key le (Seq.tail s)))

let count_cons (#t: eqtype) (y x: t) (s: Seq.seq t)
  : Lemma (Seq.count y (Seq.cons x s) == (if x = y then 1 else 0) + Seq.count y s)
  = SP.head_cons x s; SP.lemma_tl x s

let rec insert_count (#t: eqtype) (#k: Type) (key: t -> k) (le: k -> k -> bool) (x: t)
                     (s: Seq.seq t) (y: t)
  : Lemma (ensures Seq.count y (insert key le x s) == (if x = y then 1 else 0) + Seq.count y s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then count_cons y x s
    else if le (key x) (key (Seq.head s)) then count_cons y x s
    else begin
      insert_count key le x (Seq.tail s) y;
      count_cons y (Seq.head s) (insert key le x (Seq.tail s));
      count_cons y (Seq.head s) (Seq.tail s);
      SP.cons_head_tail s
    end

let rec sort_by_count #t #k key le s x
  : Lemma (ensures Seq.count x (sort_by key le s) == Seq.count x s) (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      sort_by_count key le (Seq.tail s) x;
      insert_count key le (Seq.head s) (sort_by key le (Seq.tail s)) x
    end

let rec index_mem (#t: eqtype) (s: Seq.seq t) (i: nat { i < Seq.length s })
  : Lemma (ensures SP.mem (Seq.index s i) s) (decreases i)
  = if i = 0 then () else index_mem (Seq.tail s) (i - 1)

let forall_of_mem (#t: eqtype) (s1 s2: Seq.seq t) (p: t -> bool)
  : Lemma (requires (forall (i: nat { i < Seq.length s1 }). p (Seq.index s1 i)) /\
                    (forall x. SP.mem x s2 ==> SP.mem x s1))
          (ensures forall (i: nat { i < Seq.length s2 }). p (Seq.index s2 i))
  = SP.lemma_mem_count s1 p;
    introduce forall (i: nat { i < Seq.length s2 }). p (Seq.index s2 i)
    with index_mem s2 i

let sort_by_forall #t #k key le s p
  = let s' = sort_by key le s in
    introduce forall x. SP.mem x s' <==> SP.mem x s with sort_by_count key le s x;
    introduce (forall (i: nat { i < Seq.length s }). p (Seq.index s i)) ==>
              (forall (i: nat { i < Seq.length s' }). p (Seq.index s' i))
    with forall_of_mem s s' p;
    introduce (forall (i: nat { i < Seq.length s' }). p (Seq.index s' i)) ==>
              (forall (i: nat { i < Seq.length s }). p (Seq.index s i))
    with forall_of_mem s' s p

let lower_bound (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (b: k) (s: Seq.seq t) : prop =
  forall (i: nat). i < Seq.length s ==> le b (key (Seq.index s i))

let lower_bound_cons (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (b: k) (x: t) (s: Seq.seq t)
  : Lemma (requires le b (key x) /\ lower_bound key le b s)
          (ensures lower_bound key le b (Seq.cons x s))
  = assert (forall (i: nat). 0 < i /\ i < Seq.length s + 1 ==> Seq.index (Seq.cons x s) i == Seq.index s (i - 1))

let sorted_cons (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (x: t) (s: Seq.seq t)
  : Lemma (requires lower_bound key le (key x) s /\ sorted key le s)
          (ensures sorted key le (Seq.cons x s))
  = assert (forall (i: nat). 0 < i /\ i < Seq.length s + 1 ==> Seq.index (Seq.cons x s) i == Seq.index s (i - 1))

let rec insert_lb (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (b: k) (x: t) (s: Seq.seq t)
  : Lemma (requires le b (key x) /\ lower_bound key le b s)
          (ensures lower_bound key le b (insert key le x s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if le (key x) (key (Seq.head s)) then lower_bound_cons key le b x s
    else begin
      insert_lb key le b x (Seq.tail s);
      lower_bound_cons key le b (Seq.head s) (insert key le x (Seq.tail s))
    end

let sorted_tail (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (s: Seq.seq t { Seq.length s > 0 })
  : Lemma (requires sorted key le s)
          (ensures sorted key le (Seq.tail s) /\ lower_bound key le (key (Seq.head s)) (Seq.tail s))
  = ()

let rec insert_sorted (#t #k: Type) (key: t -> k) (le: k -> k -> bool) (x: t) (s: Seq.seq t)
  : Lemma (requires total_preorder le /\ sorted key le s)
          (ensures sorted key le (insert key le x s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      sorted_tail key le s;
      if le (key x) (key (Seq.head s)) then begin
        let h = Seq.head s in
        introduce forall (i: nat). i < Seq.length s ==> le (key x) (key (Seq.index s i))
        with (if i > 0 && i < Seq.length s
              then assert (le (key x) (key h) /\ le (key h) (key (Seq.index s i)))
              else ());
        sorted_cons key le x s
      end else begin
        let tl = Seq.tail s in
        insert_sorted key le x tl;
        insert_lb key le (key (Seq.head s)) x tl;
        sorted_cons key le (Seq.head s) (insert key le x tl)
      end
    end

let rec sort_by_sorted #t #k key le s
  : Lemma (requires total_preorder le) (ensures sorted key le (sort_by key le s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      sort_by_sorted key le (Seq.tail s);
      insert_sorted key le (Seq.head s) (sort_by key le (Seq.tail s))
    end

/// The model: a fresh array holding the sorted contents.
///
/// MODELING AXIOM: see the interface. The body copies and sorts in the model only.
fn order_by_to_list (#t #k: Type0) (a: array t) (key: t -> k) (le: k -> k -> bool)
                    (#p: perm) (#s: Ghost.erased (Seq.seq t))
  preserves A.pts_to a #p s
  returns  r : array t
  ensures  A.pts_to r (sort_by key le s)
{
  admit ()
}
