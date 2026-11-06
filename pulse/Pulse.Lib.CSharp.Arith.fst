module Pulse.Lib.CSharp.Arith

/// Specification-level integer arithmetic.
///
/// Two things live here, and they are the same kind of thing.
///
/// **C#'s `/` and `%`.** These round toward zero where F*'s round toward minus
/// infinity, so a specification written in C# syntax needs `cdiv`/`crem` to mean
/// what the C# means (R6.4a). The *program* side of `/` and `%` is already
/// faithful — `Pulse.Lib.CSharp.Int32` carries the machine obligations, a
/// non-zero divisor and a representable result — and this is its spec-level
/// counterpart.
///
/// **Facts about `%` itself**, such as what makes a moving origin sound. These
/// carry SMT patterns, so they apply wherever a C# `%` appears.
///
/// Both are about integers — not about the type the arithmetic was computed at,
/// and not about whatever data structure motivated them. Like
/// `Pulse.Lib.CSharp.Seq`, this is a place where proof difficulty the emitter
/// must not invent (doc/translation.md §0, rule 3) is allowed to live — but only
/// as *general-purpose* lemmas, phrased over arbitrary integers and never over a
/// particular program.

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

// ---------------------------------------------------------------------------
// C#'s `/` and `%`, at the mathematical values a specification speaks.
//
// R6.4 makes a specification's arithmetic mathematical, which for `+`, `-` and `*` is
// exactly C#'s operator with the overflow obligation moved to the code. For `/` and `%`
// it is not: F*'s `/` on `int` rounds toward minus infinity and C#'s rounds toward zero,
// so `-7 / 2` is `-4` in F* and `-3` in C#, and `-7 % 2` is `1` and `-1`. A specification
// written in C# syntax has to mean the C# — otherwise `Result == x / 2` is a claim the
// reader and the prover disagree about, and the disagreement is invisible.
//
// `FStar.Int.( /- )` is ulib's truncating division, defined for exactly
// this reason ("Multiplicative operator semantics, see C11 6.5.5"); C# 6.5.5's is the
// same. `crem` is the remainder that goes with it, which is how C# defines `%` too.
// ---------------------------------------------------------------------------

/// C#'s `/`: division truncating toward zero (ECMA-334 §12.10.3).
let cdiv (a: int) (b: int { b <> 0 }) : int = FStar.Int.(a /- b)

/// C#'s `%`: the remainder that pairs with `cdiv`, so `(a/b)*b + a%b == a` and the sign
/// of the result is the sign of the dividend (ECMA-334 §12.10.4).
let crem (a: int) (b: int { b <> 0 }) : int = a - (cdiv a b) * b

/// On non-negative operands the two agree with F*'s own, which is what lets a
/// specification about unsigned quantities go on being discharged by `FStar.Math.Lemmas`
/// and by everything else stated in terms of `/` and `%`. Patterned, because the whole
/// point is that the user should not have to know the distinction exists in the case
/// where there is none.
let cdiv_nonneg (a: nat) (b: pos)
  : Lemma (cdiv a b == a / b) [SMTPat (cdiv a b)]
  = ()

let crem_nonneg (a: nat) (b: pos)
  : Lemma (crem a b == a % b) [SMTPat (crem a b)]
  = Math.lemma_div_mod a b

/// The defining equation, available whatever the signs.
let cdiv_crem (a: int) (b: int { b <> 0 })
  : Lemma ((cdiv a b) * b + crem a b == a) [SMTPat (crem a b)]
  = ()

/// A loop measure that may stop decreasing once `set` is: `m + 1` while it is clear, `0`
/// after. The iteration that sets a loop's break flag exits rather than decreasing `m`,
/// and Pulse forbids a dereference in a branch of a measure's `if` (F9), so the emitter
/// passes the flag and the measure here as arguments (doc/translation.md R27.10).
unfold let until_set (set: bool) (m: int) : int = if set then 0 else m + 1
