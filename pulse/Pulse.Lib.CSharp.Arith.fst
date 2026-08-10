module Pulse.Lib.CSharp.Arith

/// Specification-level integer arithmetic.
///
/// C#'s `/` and `%` (ECMA-334 §12.9.3, §12.9.4) are lowered to the operations of
/// `Pulse.Lib.CSharp.Int32` and friends, which carry the machine-level
/// obligations: a non-zero divisor, and a representable result. What those
/// modules do *not* carry is the mathematical reasoning a specification then
/// needs about the values — that `x % len` and `y % len` are distinct when `x`
/// and `y` are less than a period apart, say.
///
/// That reasoning is about integers, not about the type they were computed at
/// and not about whatever data structure motivated it, so it lives in its own
/// module. Like `Pulse.Lib.CSharp.Seq`, this is a place where proof difficulty
/// the emitter must not invent (doc/translation.md §0, rule 3) is allowed to
/// live — but only as *general-purpose* lemmas, phrased over arbitrary integers
/// and never over a particular program.

module Math = FStar.Math.Lemmas

// ---------------------------------------------------------------------------
// Residues.
//
// A structure that stores its elements starting at an arbitrary offset and
// wraps round -- a ring buffer, a hash table with linear probing, a clock --
// addresses its cells by `offset % period`. Soundness of that addressing rests
// on two facts about `%`, stated here over arbitrary integers with no reference
// to why anyone would want them.
// ---------------------------------------------------------------------------

/// Two offsets less than a period apart have different residues.
///
/// This is what makes a moving origin sound: the cells a `count`-long window
/// covers are distinct as long as the window is shorter than the period, so a
/// write at one of them leaves the rest alone. The pattern is conjunctive ---
/// it fires only when both residues are already in play --- and the
/// precondition travels with it, so the lemma is inert everywhere it does not
/// apply.
let mod_distinct_within_period (len: pos) (x: nat) (y: nat)
  : Lemma (requires x <= y /\ y - x < len)
          (ensures  (x % len == y % len ==> x == y))
          [SMTPat (x % len); SMTPat (y % len)]
  = if x % len = y % len
    then begin
      Math.lemma_mod_sub_distr y x len;
      Math.small_mod (y - x) len
    end

/// Residues one full period apart coincide. The companion to the above: an
/// origin that has just wrapped names the same cells as one that has not.
let mod_one_period_apart (len: pos) (x: nat) (y: nat)
  : Lemma (requires x + len == y \/ y + len == x)
          (ensures  x % len == y % len)
          [SMTPat (x % len); SMTPat (y % len)]
  = if x + len = y
    then Math.lemma_mod_plus x 1 len
    else Math.lemma_mod_plus y 1 len
