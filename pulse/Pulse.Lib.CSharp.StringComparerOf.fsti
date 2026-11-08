module Pulse.Lib.CSharp.StringComparerOf

/// `NonRandomizedStringEqualityComparer.GetStringComparer(comparer)` (doc/translation.md
/// R30.18): the constructors of a string-keyed `HashSet<T>` or `Dictionary<TKey, TValue>`
/// swap the default, ordinal or ordinal-ignore-case comparer for its non-randomized
/// counterpart, and keep any other comparer (the call returns null).
///
/// TRUSTED: both `val`s below are assumptions about CoreLib's
/// `NonRandomizedStringEqualityComparer`, which the program does not verify.

module Eq = Pulse.Lib.CSharp.Equality
module Obj = Pulse.Lib.CSharp.Obj
module SC = Pulse.Lib.CSharp.StringComparers

/// `GetStringComparer(comparer)`, of the comparer as an `object`.
val string_comparer (o: Obj.obj) : option Eq.handle

/// What it returns for a comparer of strings is non-randomized and has that comparer's
/// equality. The code calls it only when the element type is `string`.
val string_comparer_equals (#t: Type0) (c h: Eq.handle) (x y: t)
  : Lemma (requires Eq.type_of t == Eq.type_of string /\ string_comparer (Obj.box (Some c)) == Some h)
          (ensures SC.is_non_randomized h /\ Eq.equals h x y == Eq.equals c x y)
          [SMTPat (string_comparer (Obj.box (Some c))); SMTPat (Eq.equals #t h x y)]
