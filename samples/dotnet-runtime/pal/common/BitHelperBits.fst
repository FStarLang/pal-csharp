module BitHelperBits

(* The bitmap `BitHelper` keeps over a span of `int`s (dotnet/runtime#133116, doc/translation.md
   §37): bit `p` is bit `p % 32` of word `p / 32`, the bit `1 << (p % 32)` selects. *)

module I32 = FStar.Int32
module U32 = FStar.UInt32
module CI = Pulse.Lib.CSharp.Int32
module Cast = FStar.Int.Cast

/// `1 << k`, as C#'s unchecked shift computes it (R34.12).
let mask (k: nat{k < 32}) : I32.t = CI.shift_left_wrap 1l (U32.uint_to_t k)

/// Bit `k` of `w`, counting from the least significant.
let bit (w: I32.t) (k: nat{k < 32}) : bool = FStar.Int.nth #32 (I32.v w) (31 - k)

/// The bits of the words `ws`.
let bits (ws: Seq.seq I32.t) : Seq.seq bool =
  Seq.init (32 * Seq.length ws) (fun (p: nat{p < 32 * Seq.length ws}) -> bit (Seq.index ws (p / 32)) (p % 32))

/// Every word is zero.
let zero (ws: Seq.seq I32.t) : prop =
  forall (i: nat). {:pattern (Seq.index ws i)} i < Seq.length ws ==> Seq.index ws i == 0l

/// `MarkBit(p)`: bit `p` set, when the words hold it.
let set_bit (ws: Seq.seq I32.t) (p: int) : Seq.seq I32.t =
  if 0 <= p && p / 32 < Seq.length ws
  then Seq.upd ws (p / 32) (I32.logor (Seq.index ws (p / 32)) (mask (p % 32)))
  else ws

/// `MarkBit` keeps the number of words.
let set_bit_length (ws: Seq.seq I32.t) (p: int)
  : Lemma (Seq.length (set_bit ws p) == Seq.length ws)
          [SMTPat (set_bit ws p)]
  = ()

/// `IsMarked(p)`: the words hold bit `p`, and it is set.
let marked (ws: Seq.seq I32.t) (p: int) : bool =
  0 <= p && p / 32 < Seq.length ws && bit (Seq.index ws (p / 32)) (p % 32)

(* The mask has exactly bit `k`. *)
let mask_nth (k: nat{k < 32}) (j: nat{j < 32})
  : Lemma (bit (mask k) j == (j = k))
  = assert_norm (pow2 32 == 4294967296);
    assert_norm (pow2 31 == 2147483648);
    FStar.Math.Lemmas.pow2_le_compat 31 k;
    if k < 31 then begin
      FStar.Math.Lemmas.pow2_lt_compat 31 k;
      FStar.Math.Lemmas.small_mod (pow2 k) (pow2 32);
      assert (I32.v (mask k) == pow2 k);
      FStar.Int.pow2_to_vec_lemma #32 k (31 - j)
    end else begin
      assert (I32.v (mask k) == - pow2 31);
      assert (FStar.Int.to_uint #32 (I32.v (mask k)) == pow2 31);
      FStar.UInt.pow2_to_vec_lemma #32 31 (31 - j)
    end

let logand_mask (w: I32.t) (k: nat{k < 32})
  : Lemma ((I32.logand w (mask k) <> 0l) == bit w k /\
           (not (I32.eq (I32.logand w (mask k)) 0l)) == bit w k)
          [SMTPat (I32.logand w (mask k))]
  = let r = I32.logand w (mask k) in
    let aux (j: nat{j < 32}) : Lemma (FStar.Int.nth #32 (I32.v r) (31 - j) == (j = k && bit w k))
      = mask_nth k j in
    FStar.Classical.forall_intro aux;
    if bit w k then begin
      assert (FStar.Int.nth #32 (I32.v r) (31 - k));
      FStar.Int.zero_nth_lemma #32 (31 - k);
      if I32.v r = 0 then assert (FStar.Int.nth #32 (FStar.Int.zero 32) (31 - k) == false)
    end else begin
      let z (i: nat{i < 32}) : Lemma (FStar.Int.nth #32 (I32.v r) i == FStar.Int.nth #32 (FStar.Int.zero 32) i)
        = FStar.Int.zero_nth_lemma #32 i; aux (31 - i) in
      FStar.Classical.forall_intro z;
      FStar.Int.nth_lemma #32 (I32.v r) (FStar.Int.zero 32);
      I32.v_inj r 0l
    end

let logor_mask (w: I32.t) (k: nat{k < 32}) (j: nat{j < 32})
  : Lemma (bit (I32.logor w (mask k)) j == (j = k || bit w j))
  = mask_nth k j

let zero_bit (j: nat{j < 32})
  : Lemma (bit 0l j == false)
  = FStar.Int.zero_nth_lemma #32 (31 - j)

(* How `MarkBit` and `IsMarked` compute word `p / 32` and mask `1 << (p % 32)` from a
   non-negative `p`: through `uint`, as `(uint)p / IntSize` and `(uint)p % IntSize`. *)

let uint_of_nonneg (n: I32.t)
  : Lemma (requires I32.v n >= 0)
          (ensures U32.v (Cast.int32_to_uint32 n) == I32.v n)
          [SMTPat (Cast.int32_to_uint32 n)]
  = ()

let word_index (p: I32.t)
  : Lemma (requires I32.v p >= 0)
          (ensures U32.v (U32.div (Cast.int32_to_uint32 p) 32ul) == I32.v p / 32 /\
                   I32.v (Cast.uint32_to_int32 (U32.div (Cast.int32_to_uint32 p) 32ul)) == I32.v p / 32)
          [SMTPat (U32.div (Cast.int32_to_uint32 p) 32ul)]
  = ()

let bit_mask (p: I32.t)
  : Lemma (requires I32.v p >= 0)
          (ensures CI.shift_left_wrap 1l (Cast.int32_to_uint32 (Cast.uint32_to_int32 (U32.rem (Cast.int32_to_uint32 p) 32ul)))
                   == mask (I32.v p % 32))
          [SMTPat (U32.rem (Cast.int32_to_uint32 p) 32ul)]
  = let r = U32.rem (Cast.int32_to_uint32 p) 32ul in
    assert (U32.v r == I32.v p % 32);
    assert (U32.v (Cast.int32_to_uint32 (Cast.uint32_to_int32 r)) == U32.v r);
    U32.v_inj (Cast.int32_to_uint32 (Cast.uint32_to_int32 r)) (U32.uint_to_t (I32.v p % 32))

(* What `CheckUniqueAndUnfoundElements` needs of the bitmap. *)

/// Zero words hold no bit.
let zero_bits (ws: Seq.seq I32.t)
  : Lemma (requires zero ws)
          (ensures (forall (p: nat). p < Seq.length (bits ws) ==> Seq.index (bits ws) p == false))
  = let aux (p: nat{p < Seq.length (bits ws)}) : Lemma (Seq.index (bits ws) p == false)
      = zero_bit (p % 32) in
    FStar.Classical.forall_intro aux

/// `MarkBit(p)` sets bit `p` alone.
let set_bits (ws: Seq.seq I32.t) (p: int)
  : Lemma (requires 0 <= p /\ p < Seq.length (bits ws))
          (ensures bits (set_bit ws p) == Seq.upd (bits ws) p true)
  = let l = bits (set_bit ws p) in
    let r = Seq.upd (bits ws) p true in
    let aux (q: nat{q < Seq.length l}) : Lemma (Seq.index l q == Seq.index r q)
      = logor_mask (Seq.index ws (p / 32)) (p % 32) (q % 32);
        FStar.Math.Lemmas.euclidean_division_definition p 32;
        FStar.Math.Lemmas.euclidean_division_definition q 32 in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro l r

/// `IsMarked(p)` reads bit `p`.
let marked_bits (ws: Seq.seq I32.t) (p: int)
  : Lemma (requires 0 <= p /\ p < Seq.length (bits ws))
          (ensures marked ws p == Seq.index (bits ws) p)
  = ()

/// `IsMarked(p)` and `MarkBit(p)` at any `p`: past the words, `IsMarked` reads false and
/// `MarkBit` does nothing. The method before dotnet/runtime#133116 relies on this
/// (samples/dotnet-runtime/SORTEDSET-PR133116.md §3).
let bits_at (ws: Seq.seq I32.t) (p: int)
  : Lemma (requires 0 <= p)
          (ensures (p < Seq.length (bits ws) ==>
                      marked ws p == Seq.index (bits ws) p /\ bits (set_bit ws p) == Seq.upd (bits ws) p true) /\
                   (p >= Seq.length (bits ws) ==> marked ws p == false /\ set_bit ws p == ws))
  = if p < Seq.length (bits ws) then set_bits ws p

/// The bits of `n` words are `32 * n`.
let bits_length (ws: Seq.seq I32.t)
  : Lemma (Seq.length (bits ws) == 32 * Seq.length ws)
          [SMTPat (Seq.length (bits ws))]
  = ()

// `ToIntArrayLength(n)` words hold at least `n` bits.
let words_cover (n: int)
  : Lemma (requires n >= 0) (ensures n <= 32 * (if n > 0 then (n - 1) / 32 + 1 else 0))
  = ()
