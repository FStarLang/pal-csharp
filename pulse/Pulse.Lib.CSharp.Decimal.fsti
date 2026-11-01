module Pulse.Lib.CSharp.Decimal

/// `System.Decimal`, as the exact rational it denotes.
///
/// MODELING AXIOM. A .NET decimal is `m * 10^-s` with `|m| < 2^96` and `0 <= s <= 28`,
/// so every decimal embeds exactly into the rationals; `v` is that embedding. Two decimals
/// with the same value but different scales (`1.0m`, `1.00m`) are distinct bit patterns
/// that C#'s `==` and every comparison operator identify, and so does this model: a
/// `decimal` *is* its value (`v_inj`). Nothing in the translated subset observes the scale
/// (no `ToString`, no `GetBits`), which is what makes the identification sound.
///
/// The comparisons are total functions returning `bool`, because C# evaluates them;
/// each is specified by the order of `FStar.Real`, so the order laws are the reals' own.
/// No arithmetic is modelled: rounding and overflow would need a specification that
/// nothing here requires.

open FStar.Real

val decimal : eqtype

val v (d: decimal) : real

val v_inj (a b: decimal)
  : Lemma (requires v a == v b) (ensures a == b)

/// The exact range of `System.Decimal`: `|v| <= 2^96 - 1`.
let max_value : int = pow2 96 - 1

val v_range (d: decimal)
  : Lemma (of_int (- max_value) <=. v d /\ v d <=. of_int max_value)

/// A decimal literal `n / 10^s`: C# rejects a literal outside the range at compile time.
val lit (n: int) (s: nat { s <= 28 /\ - max_value <= n /\ n <= max_value })
  : d: decimal { v d *. of_int (FStar.Math.Lib.powx 10 s) == of_int n }

val lt (a b: decimal) : r: bool { r <==> v a <. v b }
val le (a b: decimal) : r: bool { r <==> v a <=. v b }
val gt (a b: decimal) : r: bool { r <==> v a >. v b }
val ge (a b: decimal) : r: bool { r <==> v a >=. v b }
