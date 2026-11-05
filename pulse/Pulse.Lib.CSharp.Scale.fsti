module Pulse.Lib.CSharp.Scale

module I32 = FStar.Int32

/// `(int)((double)n * c)` for a literal `0 <= c <= 1` (doc/translation.md R26.6).
/// The translation has no floating point, so the product is not computed in the
/// proof: what is assumed (trusted) is only that scaling an `int` by a factor in
/// `[0, 1]` and truncating towards zero lands between `0` and `n`. Exact for every
/// `int` and every such literal, since a double holds every `int` exactly and the
/// rounded product of two numbers of magnitude at most `|n|` and `1` cannot exceed
/// `|n|`.
val scale_unit (n: I32.t)
  : r: I32.t { (I32.v n >= 0 ==> 0 <= I32.v r /\ I32.v r <= I32.v n) /\
               (I32.v n < 0 ==> I32.v n <= I32.v r /\ I32.v r <= 0) }
