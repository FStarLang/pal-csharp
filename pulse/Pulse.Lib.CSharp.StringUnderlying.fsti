module Pulse.Lib.CSharp.StringUnderlying

/// `IInternalStringEqualityComparer.GetUnderlyingEqualityComparer(c)` (doc/translation.md
/// R30.34): the public comparer a string-keyed `HashSet<T>` or `Dictionary<TKey, TValue>`
/// returns from its `Comparer` property in place of the non-randomized (or randomized)
/// comparer it swapped in, or `c` itself.
///
/// TRUSTED: both `val`s below are assumptions about CoreLib, which the program does not
/// verify.

module Eq = Pulse.Lib.CSharp.Equality

val underlying (c: Eq.handle) : Eq.handle

/// It has `c`'s equality.
val underlying_equals (#t: Type0) (c: Eq.handle) (x y: t)
  : Lemma (Eq.equals (underlying c) x y == Eq.equals c x y)
          [SMTPat (Eq.equals #t (underlying c) x y)]

/// `string` is a reference type (the C# type system).
val string_not_value_type (t: Type0)
  : Lemma (requires Eq.type_of t == Eq.type_of string)
          (ensures not (Eq.is_value_type (Eq.type_of t)))
          [SMTPat (Eq.is_value_type (Eq.type_of t))]
