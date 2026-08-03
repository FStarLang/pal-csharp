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

/// R9.13. **The dynamic-type assumption.** A CLR reference denotes the object it was
/// made from: an upcast changes only the static type, and recovering the object yields
/// the one that was stored.
///
/// `FStar.Dyn.undyn` models the recovery but ships in `Dv` with no equation relating its
/// result to its argument, and no such equation is provable, since `Dv` results cannot be
/// equated in specifications. So the recovery has to be assumed, and this is the whole of
/// what §9's encoding assumes beyond F*'s own logic.
///
/// Stated in `stt` rather than `stt_div` deliberately (F30b): in `stt_div` every
/// postcondition is inhabited by a computation that hangs, so the axiom would say nothing
/// at all. Here it says exactly one thing beyond what F\* can prove -- that the recovery
/// terminates and is faithful -- which is what the CLR object header is for.
///
/// It does **not** imply injectivity of `FStar.Dyn.mkdyn`: each `recover` is a separate
/// computation, and `ShapeHierarchy.fst` §3 pins the injectivity F\* will not give.
val recover (#a: Type u#a) (#x: FStar.Ghost.erased a)
            (d: FStar.Dyn.dyn { d == FStar.Dyn.mkdyn (FStar.Ghost.reveal x) })
  : Pulse.Lib.Core.stt a Pulse.Lib.Core.emp (fun y -> Pulse.Lib.Core.pure (y == FStar.Ghost.reveal x))
