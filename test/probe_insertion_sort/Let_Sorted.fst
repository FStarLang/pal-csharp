module Let_Sorted

/// DERIVED, NOT AUTHORED.
///
/// This module is the result of hand-executing doc/translation.md on
///
///     [Spec]
///     [Requires("0 <= lo && lo <= hi && hi <= a.Length")]
///     static bool Sorted(int[] a, int lo, int hi) =>
///         Pal.Forall((int i, int j) =>
///             Pal.Implies(lo <= i && i < j && j < hi, a[i] <= a[j]));
///
/// Rules used: R2.1 (naming: `Sorted` -> `spec_Sorted`, parameter `p` ->
/// `var_p`), R4.6 (`[Spec]` methods are spec-only: `int` parameters become
/// mathematical `int`, `T[]` parameters become `Seq.seq`, and `[Requires]`
/// becomes a refinement on the last binder), R6.5 (`a[i]` in spec position is
/// `Seq.index s i`), R6.7 (`Pal.Forall` -> `forall`, `Pal.Implies` -> `==>`).
///
/// Nothing here is idiomatic F*: an F* programmer would write `sorted` over a
/// slice, or reuse `FStar.Seq.Properties.sorted`. The point of the probe is to
/// find out whether the *mechanical* output is provable.

module Seq = FStar.Seq

let spec_Sorted (var_a: Seq.seq FStar.Int32.t)
                (var_lo: int)
                (var_hi: int { 0 <= var_lo /\ var_lo <= var_hi /\ var_hi <= Seq.length var_a })
  : prop
  = forall (var_i: int) (var_j: int).
      (var_lo <= var_i /\ var_i < var_j /\ var_j < var_hi)
      ==> FStar.Int32.v (Seq.index var_a var_i) <= FStar.Int32.v (Seq.index var_a var_j)
