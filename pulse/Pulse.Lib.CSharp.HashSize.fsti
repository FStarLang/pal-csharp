module Pulse.Lib.CSharp.HashSize

/// The table sizes the hashing collections grow to (doc/translation.md §30, R30.5):
/// `HashHelpers.GetPrime` and `HashHelpers.GetPrimeAtLeast`. Their bodies search a table
/// of primes and then trial-divide upward without a bound, so they are not verified;
/// each `val` here is TRUSTED, and states only what the collections rely on.

module I32 = FStar.Int32

/// `HashHelpers.MaxPrimeArrayLength`, the largest prime below `Array.MaxLength`.
let max_prime : int = 0x7FFFFFC3

/// The result of `GetPrime(min)` / `GetPrimeAtLeast(min)` for `min >= 0` (a negative
/// `min` throws, and every caller is shown not to pass one): at least `min` and at least
/// 3, and no more than `max_prime` when `min` is not (that prime is itself in range of
/// both searches, which go upward from `min`).
let size_ok (min r: int) : prop =
  r >= min /\ r >= 3 /\ (min <= max_prime ==> r <= max_prime)

/// `HashHelpers.IsPrime(n)`, which asserts `n >= 3`: whether `n` is prime. Nothing is
/// assumed about it but that the two searches below return a size it holds of.
val is_prime (n: I32.t{I32.v n >= 3}) : bool

val get_prime (min: I32.t{I32.v min >= 0})
  : r: I32.t{size_ok (I32.v min) (I32.v r) /\ is_prime r}

val get_prime_at_least (min: I32.t{I32.v min >= 0})
  : r: I32.t{size_ok (I32.v min) (I32.v r) /\ is_prime r}

/// A table size: at least 3 and prime.
let prime_size (n: int) : prop =
  3 <= n /\ n <= 0x7FFFFFFF /\ is_prime (I32.int_to_t n)
