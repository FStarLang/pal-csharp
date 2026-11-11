module Pulse.Lib.CSharp.StringComparers

/// CoreLib's non-randomized string comparers (doc/translation.md R30.6). A string-keyed
/// `HashSet<T>` or `Dictionary<TKey, TValue>` built with the default, ordinal or
/// ordinal-ignore-case comparer hashes with a cheaper, non-randomized function, and switches
/// to the randomized comparer with the same equality when a chain grows too long.
///
/// TRUSTED: every `val` below is an assumption about CoreLib's
/// `NonRandomizedStringEqualityComparer`, which the program does not verify.

module Eq = Pulse.Lib.CSharp.Equality

/// `c is NonRandomizedStringEqualityComparer`.
val is_non_randomized (c: Eq.handle) : bool

/// `c.GetRandomizedEqualityComparer()`.
val randomized (c: Eq.handle) : Eq.handle

/// The randomized comparer deems equal what the non-randomized one does.
val randomized_equals (#t: Type0) (c: Eq.handle) (x y: t)
  : Lemma (requires is_non_randomized c)
          (ensures Eq.equals (randomized c) x y == Eq.equals c x y)
          [SMTPat (Eq.equals #t (randomized c) x y)]

/// A non-randomized comparer's equality (ordinal, or ordinal ignoring case) is reflexive.
val non_randomized_refl (#t: Type0) (c: Eq.handle) (x: t)
  : Lemma (requires is_non_randomized c)
          (ensures Eq.equals c x x)
          [SMTPat (is_non_randomized c); SMTPat (Eq.equals #t c x x)]
