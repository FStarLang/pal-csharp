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
