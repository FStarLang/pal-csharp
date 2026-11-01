module Pulse.Lib.CSharp.Opaque

/// A value of a C# type the translation does not model: a delegate (doc/translation.md §20).
///
/// Verified code may hold such a value and pass it on, and nothing else: it cannot call
/// it, compare it or look inside it. So nothing is assumed about it either. The type is
/// indexed by the C# type's name only so that two different delegate types are not the
/// same F* type.
val delegate (name: string) : Type0

/// A method-group conversion, `ResourceStrings.TierBandOverlap` passed where a
/// `Func<CultureInfo, string>` is expected. Allocating the delegate has no effect that
/// verified code can observe; which value it is, is left uninterpreted.
val method_group (#name: string) (m: string) : delegate name
