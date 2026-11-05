module Pulse.Lib.CSharp.Casts

open Pulse.Lib.CSharp.Assumptions

module C = FStar.Int.Cast
module I32 = FStar.Int32
module SZ = FStar.SizeT

let int32_to_sizet (x: I32.t) =
  SZ.uint32_to_sizet (C.int32_to_uint32 x)

let sizet_to_int32 (x: SZ.t) =
  C.uint32_to_int32 (SZ.sizet_to_uint32 x)

let int_logand_as_uint (a b: FStar.Int.int_t 32)
  : Lemma (FStar.Int.logand a b ==
           FStar.Int.from_uint (FStar.UInt.logand (FStar.Int.to_uint a) (FStar.Int.to_uint b)))
  = ()

let byte_mask_ff b =
  let x : FStar.Int.int_t 32 = FStar.UInt8.v b in
  int_logand_as_uint x 255;
  FStar.UInt.logand_mask #32 x 8;
  FStar.Math.Lemmas.small_mod (FStar.UInt8.v b) 256

let byte_mask_ff_bound b =
  byte_mask_ff b;
  FStar.Math.Lemmas.small_mod (FStar.UInt8.v b) 4294967296

let logor_shift_disjoint x y m =
  let n = FStar.UInt32.v m in
  let a = FStar.UInt32.v x in
  let b = FStar.UInt32.v y in
  FStar.Math.Lemmas.pow2_plus n (32 - n);
  FStar.Math.Lemmas.lemma_mult_lt_right (pow2 n) a (pow2 (32 - n));
  FStar.Math.Lemmas.small_mod (a * pow2 n) (pow2 32);
  FStar.Math.Lemmas.multiple_modulo_lemma a (pow2 n);
  FStar.UInt.logor_disjoint #32 (a * pow2 n) b n

let shift_right_nonneg a s =
  FStar.UInt.shift_right_value_lemma #32 a s;
  assert (FStar.Int.to_vec #32 a == FStar.UInt.to_vec #32 a);
  FStar.Math.Lemmas.lemma_div_le a (pow2 31) (pow2 s);
  FStar.Math.Lemmas.pow2_le_compat 31 0

let small_pow2_eq (k: nat) : Lemma (small_pow2 k == pow2 k) =
  assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 4 == 16 /\
               pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128 /\ pow2 8 == 256)

let int32_shift_right_nonneg a k =
  shift_right_nonneg (FStar.Int32.v a) (FStar.Int32.v k);
  small_pow2_eq (FStar.Int32.v k)
