module ConversionFacts
#lang-pulse

(* §0 probe for §13, numeric width conversions.

   The question a C# cast asks is not the question C# arithmetic asks. pal-csharp proves
   arithmetic does not overflow, because C# defines overflow as wrapping and a wrapping
   `+` is almost always a bug. An explicit `(byte)v`, by contrast, is the programmer
   *asking* for truncation: C#'s default `unchecked` context defines the conversion to
   truncate, and there is nothing accidental about it.

   So the two are translated differently, and this file pins the difference before any
   rule is written. Every fact below is checked by F*, not asserted in prose. *)

open Pulse
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I32 = FStar.Int32
module I64 = FStar.Int64
module C = FStar.Int.Cast

(* ------------------------------------------------------------------------- *)
(* F46. Widening is total and value-preserving. No precondition, no proof
   obligation, and the value is *equal* -- not merely congruent. This is what
   makes `(uint)someByte` free, which is the operation every byte-oriented loop
   in real C# performs on the way into an accumulator. *)

let widen_u8_u32_exact (b: U8.t)
  : Lemma (U32.v (C.uint8_to_uint32 b) == U8.v b)
  = ()

let widen_u8_u64_exact (b: U8.t)
  : Lemma (U64.v (C.uint8_to_uint64 b) == U8.v b)
  = ()

let widen_u32_u64_exact (x: U32.t)
  : Lemma (U64.v (C.uint32_to_uint64 x) == U32.v x)
  = ()

(* F47. A widened byte is bounded, and the bound is what an overflow proof needs.
   This is the fact that carries the Adler-32 accumulator argument: each addend is
   at most 255, so 3800 of them are at most 969000. *)

let widen_u8_u32_bounded (b: U8.t)
  : Lemma (U32.v (C.uint8_to_uint32 b) <= 255)
  = ()

(* ------------------------------------------------------------------------- *)
(* F48. Narrowing is modular, and that is exactly C#'s `unchecked` truncation --
   not an approximation of it. So the cast is always well defined and never
   carries a proof obligation of its own. *)

let narrow_u32_u8_modular (x: U32.t)
  : Lemma (U8.v (C.uint32_to_uint8 x) == U32.v x % 256)
  = ()

(* F49. ...and when the value is known to be in range, modular narrowing is exact.
   This is what lets a user recover `(byte)v == v` by proving `0 <= v < 256`
   themselves, rather than the translator demanding it up front. The translator
   invents no precondition; the user states one when they want the stronger fact. *)

let narrow_u32_u8_exact_in_range (x: U32.t)
  : Lemma (requires U32.v x < 256)
          (ensures  U8.v (C.uint32_to_uint8 x) == U32.v x)
  = ()

(* F50. Round trip: widening then narrowing is the identity, unconditionally.
   Needed wherever a byte is lifted into an accumulator and later stored back. *)

let widen_narrow_roundtrip (b: U8.t)
  : Lemma (C.uint32_to_uint8 (C.uint8_to_uint32 b) == b)
  = FStar.Math.Lemmas.small_mod (U8.v b) 256;
    assert (U8.v (C.uint32_to_uint8 (C.uint8_to_uint32 b)) == U8.v b);
    U8.v_inj (C.uint32_to_uint8 (C.uint8_to_uint32 b)) b

(* ------------------------------------------------------------------------- *)
(* F51. Cross-signedness. C# reinterprets the bit pattern, and so does F*: a
   negative `int` cast to `uint` lands at its two's-complement image. Stated
   modularly, which is the only form that is true for every input. *)

let int32_to_uint32_modular (x: I32.t)
  : Lemma (U32.v (C.int32_to_uint32 x) == I32.v x % 4294967296)
  = ()

let int32_to_uint32_nonneg (x: I32.t)
  : Lemma (requires I32.v x >= 0)
          (ensures  U32.v (C.int32_to_uint32 x) == I32.v x)
  = FStar.Math.Lemmas.small_mod (I32.v x) 4294967296

(* F52. The `& 0xff` idiom. Real byte-oriented C# writes `(uint)(b & 0xff)` even
   when `b` is already a byte, because the author is defending against sign
   extension in a language where `byte` promotes to `int`. Masking after widening
   is the identity on a widened byte, so the defensive mask costs nothing to prove
   and need not be special-cased anywhere. *)

let mask_after_widen_is_identity (b: U8.t)
  : Lemma (U32.logand (C.uint8_to_uint32 b) 0xfful == C.uint8_to_uint32 b)
  = FStar.UInt.logand_mask (U32.v (C.uint8_to_uint32 b)) 8;
    FStar.Math.Lemmas.small_mod (U8.v b) 256;
    U32.v_inj (U32.logand (C.uint8_to_uint32 b) 0xfful) (C.uint8_to_uint32 b)

(* ------------------------------------------------------------------------- *)
(* F53. The Adler-32 accumulator bound, which is the whole point of the exercise
   and is pinned here in pure arithmetic before any C# is translated.

   SharpZipLib defers the modulo for n = 3800 bytes and justifies it in a comment:
     "s1 maximally grows from 65521 to 65521 + 255 * 3800
      s2 maximally grows by 3800 * median(s1) = 2090079800 < 2^31"

   The claimed figure is wrong -- the true supremum is 2090626020, larger by
   546220 -- but the conclusion holds. Both halves are stated below, so the proof
   records what is actually true rather than what the comment claims. *)

let adler_s1_bound (k: nat)
  : Lemma (requires k <= 3800)
          (ensures  65520 + 255 * k <= 1034520)
  = ()

(* The triangular sum is what the informal argument approximated with a "median". *)
let rec tri (n: nat) : nat = if n = 0 then 0 else n + tri (n - 1)

let rec tri_closed (n: nat)
  : Lemma (ensures 2 * tri n == n * (n + 1))
          (decreases n)
  = if n = 0 then () else tri_closed (n - 1)

(* s2 <= 65520 + sum_{k=1..n} (65520 + 255k) = 65520 + 65520n + 255 * tri n *)
let adler_s2_bound ()
  : Lemma (65520 + 65520 * 3800 + 255 * tri 3800 == 2090626020 /\
           2090626020 < 2147483648 /\
           2090626020 < 4294967296)
  = tri_closed 3800

(* And the figure the comment claims is strictly smaller than the truth, so the
   comment understates the maximum -- the direction that matters, because an
   understated bound is the one that could have been unsafe. *)
let adler_comment_understates ()
  : Lemma (2090079800 < 2090626020)
  = ()

(* ------------------------------------------------------------------------- *)
(* F54. The mask idiom as it actually appears, at `int` width.

   `buf[i] & 0xff` on a `byte` is not a byte operation: C# promotes both operands to
   `int` and applies `int`'s `&`. So the fact that has to be proved is about
   `FStar.Int32.logand` on a widened byte, not about `FStar.UInt8.logand` -- which is
   what makes R13.4's promotion load-bearing rather than pedantic.

   `FStar.Int` has no `logand_mask`, so the proof goes through the unsigned view: on a
   non-negative `int`, `to_uint` is the identity, and there the mask lemma applies. *)

(* `FStar.Int.logand` and `FStar.UInt.logand` are the same bit-vector operation
   viewed through different codings, and unfolding both definitions says so. *)
let int_logand_as_uint (a b: FStar.Int.int_t 32)
  : Lemma (FStar.Int.logand a b ==
           FStar.Int.from_uint (FStar.UInt.logand (FStar.Int.to_uint a) (FStar.Int.to_uint b)))
  = ()

let byte_mask_ff (b: U8.t)
  : Lemma (I32.v (I32.logand (C.uint8_to_int32 b) 255l) == U8.v b)
  = let x : FStar.Int.int_t 32 = U8.v b in
    int_logand_as_uint x 255;
    FStar.UInt.logand_mask #32 x 8;
    FStar.Math.Lemmas.small_mod (U8.v b) 256

(* F55. ...and the widened, masked byte is what the accumulator adds, so the bound the
   overflow proof needs is 255. *)

let byte_mask_ff_bound (b: U8.t)
  : Lemma (U32.v (C.int32_to_uint32 (I32.logand (C.uint8_to_int32 b) 255l)) <= 255)
  = byte_mask_ff b;
    FStar.Math.Lemmas.small_mod (U8.v b) 4294967296
