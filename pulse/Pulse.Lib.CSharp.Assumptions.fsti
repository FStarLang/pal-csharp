module Pulse.Lib.CSharp.Assumptions

open FStar.SizeT { fits, fits_u32, fits_u64, fits_u32_implies_fits }

/// Axioms about the platform pal-csharp targets. Each one is a fact about the
/// CLR, not a convenience: if any is wrong, verified programs are unsound.

/// The CLR requires a 32-bit or 64-bit address space, and `Span<T>` indices are
/// at least 32 bits wide, so `size_t` admits every 32-bit unsigned value.
assume SizeTFitsU32 : fits_u32

/// Exposed with an SMTPat so `size_t`-fits goals arising from the `int`/`size_t`
/// index bridge (`Pulse.Lib.CSharp.Casts.idx`) discharge automatically.
let sizet_fits_u32_pat (x:int)
  : Lemma
    (requires 0 <= x /\ x < FStar.UInt.max_int 32)
    (ensures fits x)
    [SMTPat (fits x)]
  = fits_u32_implies_fits x

/// `System.Array.Length` has type `int`, so no CLR array can hold more than
/// `Int32.MaxValue` elements. This is what lets `a.Length` be translated
/// without a representability side condition.
let max_array_length : nat = pow2 31 - 1
