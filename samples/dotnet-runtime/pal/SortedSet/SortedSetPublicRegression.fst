module SortedSetPublicRegression

module I32 = FStar.Int32
module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module D = Pulse.Lib.CSharp.TopDown
module H = Pulse.Lib.CSharp.TopDownHeap

let prefix (items: Seq.seq I32.t) (n: int) : prop =
  Seq.length items == n /\
  (forall (i: nat). i < n ==> I32.v (Seq.index items i) == i)

let snoc (items: Seq.seq I32.t) (n: FStar.Int.int_t 32)
  : Lemma (requires prefix items n)
          (ensures prefix (Seq.snoc items (I32.int_to_t n)) (n + 1))
  = ()

let grow (items: Seq.seq I32.t) (n: FStar.Int.int_t 32)
  : Lemma
      (requires prefix items n)
      (ensures S.key_index (O.default_comparer I32.t) items (I32.int_to_t n) < 0 /\
               prefix (H.inserted (O.default_comparer I32.t) items (I32.int_to_t n)) (n + 1))
  = let c = O.default_comparer I32.t in
    let item = I32.int_to_t n in
    let less (i: nat) : Lemma
        (i < Seq.length items ==> O.compare c (Seq.index items i) item < 0)
      = if i < Seq.length items then O.default_int32_order (Seq.index items i) item in
    FStar.Classical.forall_intro less;
    S.lower_bound_prefix c items item (Seq.length items);
    H.inserted_length c items item;
    let result = H.inserted c items item in
    let at (i: nat) : Lemma (i < Seq.length result ==> I32.v (Seq.index result i) == i)
      = if i < Seq.length result then D.seq_ins_index items (Seq.length items) item i in
    FStar.Classical.forall_intro at

let same (left right: Seq.seq I32.t) (n: int)
  : Lemma (requires prefix left n /\ prefix right n)
          (ensures left == right)
  = Seq.lemma_eq_intro left right

let same_hits (c: O.comparer I32.t) (left right: Seq.seq I32.t)
  : Lemma (requires Seq.equal left right)
          (ensures SortedSetCount.all_hit c left right /\ SortedSetCount.all_hit c right left)
  = Seq.lemma_eq_elim left right;
    SortedSetCount.pointwise_hits c left right
