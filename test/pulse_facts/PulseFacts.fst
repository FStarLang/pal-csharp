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

/// F8: a stateful block may appear in *term* position, as the scrutinee of a
///     `let`. This is what makes the short-circuit rule R6.3 compositional:
///     `e1 && e2` lowers to the same `let t = if [[e1]] { [[e2]] } else { false }`
///     whether it appears in a loop guard, an `if` condition or an assignment
///     right-hand side, with no context-dependent special case.
///
/// F9: a `decreases` measure may dereference a mutable local, but *not* under
///     an `if`. `decreases (if !b then 0 else I32.v !r)` is rejected ("Expected
///     type FStar.Int32.t but !r has type fn ..."), because the `!` sugar is
///     only elaborated outside the branches. A conditional measure must
///     therefore keep its dereferences out of the branches -- or, better, the
///     program should be written so a straight-line measure works.
fn short_circuit_in_term_position (r: R.ref bool) (q: R.ref bool)
requires exists* b c. R.pts_to r b ** R.pts_to q c
ensures  exists* b c. R.pts_to r b ** R.pts_to q c
{
  let b = !r;
  let t = if (b) { let c = !q; (not c) } else { false };
  r := t;
}

fn decreases_conditional_without_deref (r: R.ref FStar.Int32.t) (b: R.ref bool)
requires exists* v c. R.pts_to r v ** R.pts_to b c ** pure (FStar.Int32.v v >= 0)
ensures  exists* v c. R.pts_to r v ** R.pts_to b c
{
  while (let c = !b; (not c))
  invariant exists* v c. R.pts_to r v ** R.pts_to b c ** pure (FStar.Int32.v v >= 0)
  decreases ((FStar.Int32.v !r + 1) * (if !b then 0 else 1))
  {
    b := true;
  };
  ()
}
