module Pulse.Lib.CSharp.Int32

/// The C# `int` type.
///
/// ECMA-334 §12.9 gives `int` arithmetic two contexts: `checked`, which throws
/// `OverflowException`, and `unchecked` (the default), which wraps. pal-csharp
/// proves *exception freedom*, and does so uniformly by imposing a no-overflow
/// proof obligation on every arithmetic operation. That obligation is sound for
/// both contexts at once: where no overflow occurs, `checked` and `unchecked`
/// agree and neither throws.
///
/// `FStar.Int32` already carries exactly those preconditions --
/// `add`/`sub`/`mul` require `size (op (v a) (v b)) 32`, and `div`/`rem`
/// additionally require a non-zero divisor and truncate toward zero as
/// ECMA-334 12.9.3 and 12.9.4 specify -- so this module re-exports it and adds
/// only the C#-facing vocabulary.

include FStar.Int32

module I32 = FStar.Int32

let int32 = I32.t

/// The specification-level value of an `int`.
let as_int (x: I32.t) : int = I32.v x

/// `System.Int32.MinValue` and `System.Int32.MaxValue`.
let min_value : int = FStar.Int.min_int I32.n
let max_value : int = FStar.Int.max_int I32.n

/// The shape of every `int` arithmetic proof obligation the emitter generates:
/// the mathematical result of `op` on the operands' values is representable.
let no_overflow (op : int -> int -> int) (vx vy : int) : prop =
  I32.fits (op vx vy)

/// R22.14. Two's-complement wrapping arithmetic: C#'s unchecked `+`, `-` and `*` on `int`.
let add_wrap (x y: I32.t) : I32.t = I32.int_to_t (FStar.Int.to_int_t 32 (I32.v x + I32.v y))
let sub_wrap (x y: I32.t) : I32.t = I32.int_to_t (FStar.Int.to_int_t 32 (I32.v x - I32.v y))
let mul_wrap (x y: I32.t) : I32.t = I32.int_to_t (FStar.Int.to_int_t 32 (I32.v x * I32.v y))

/// R34.12. C#'s unchecked `x << s` on `int`: the distance is taken modulo 32.
let shift_left_wrap (x: I32.t) (s: FStar.UInt32.t) : I32.t =
  I32.int_to_t (FStar.Int.to_int_t 32 (I32.v x * pow2 (FStar.UInt32.v s % 32)))

/// R34.12. Doubling a non-negative `int` with `<< 1`: the product, or the product less
/// 2^32 once it no longer fits, as the BCL's growth checks rely on.
let shift_left_wrap_one (x: I32.t)
  : Lemma (requires I32.v x >= 0)
          (ensures  I32.v (shift_left_wrap x (FStar.Int.Cast.int32_to_uint32 1l)) ==
                    (if 2 * I32.v x < pow2 31 then 2 * I32.v x else 2 * I32.v x - pow2 32))
          [SMTPat (shift_left_wrap x (FStar.Int.Cast.int32_to_uint32 1l))]
  = assert_norm (pow2 1 == 2);
    assert_norm (pow2 32 == 4294967296);
    assert_norm (pow2 31 == 2147483648);
    FStar.Math.Lemmas.lemma_mod_plus (2 * I32.v x) (-1) (pow2 32)

/// R34.12. `(uint)x`: `x`, or `x + 2^32` when `x` is negative.
let int32_to_uint32_v (x: I32.t)
  : Lemma (FStar.UInt32.v (FStar.Int.Cast.int32_to_uint32 x) ==
           (if I32.v x >= 0 then I32.v x else I32.v x + pow2 32))
          [SMTPat (FStar.UInt32.v (FStar.Int.Cast.int32_to_uint32 x))]
  = ()
