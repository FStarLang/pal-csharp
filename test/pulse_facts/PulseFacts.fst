module PulseFacts

/// Regression tests for the Pulse facts that doc/translation.md depends on.
///
/// These are NOT translation targets and NOT golden files. They pin the
/// behaviour of the *toolchain* so that facts F1-F3 in doc/translation.md
/// cannot silently regress under an F* version bump.

open Pulse
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
#lang-pulse

/// F1: a `while` condition may be a stateful statement block, so a
///     short-circuiting guard that reads memory (`i < n && a[i] > 0`)
///     needs no flag-rotation encoding. This is the shape rule R6.3
///     produces, and it is what makes insertion sort's inner-loop guard
///     `j >= 0 && a[j] > key` unremarkable.
///
/// F2: the `decreases` clause is required; removing it makes the loop
///     `stt_div`, which fails to compose with the `stt` continuation
///     ("Cannot compose computations in this divergent block").
///
/// F3: the measure may dereference a mutable local (`!i`) but may not
///     mention an invariant-bound existential.
fn scan_while_stateful_guard (a: A.array int) (n: SZ.t) (#s: erased (Seq.seq int))
requires A.pts_to a s ** pure (Seq.length s == SZ.v n)
ensures exists* s'. A.pts_to a s' ** pure (s' == reveal s)
{
  let mut i = 0sz;
  while (
    let iv = !i;
    if (SZ.lt iv n) { let x = A.op_Array_Access a iv; (x > 0) } else { false }
  )
  invariant exists* v. R.pts_to i v ** A.pts_to a s ** pure (SZ.v v <= SZ.v n)
  decreases (SZ.v n - SZ.v !i)
  {
    i := SZ.add !i 1sz;
  };
  ()
}
