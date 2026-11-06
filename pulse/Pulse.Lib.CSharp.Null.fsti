module Pulse.Lib.CSharp.Null

/// MODELING AXIOM (R25.4). Whether a value of a type the model treats as a value (a
/// type parameter, a comparer) is the null reference. Left uninterpreted: nothing the
/// model says about a value depends on it, except that `ThrowIfNull` throws exactly
/// when it holds. Shared by `Pulse.Lib.CSharp.Sorted` and `Pulse.Lib.CSharp.Equality`,
/// which is why it is a module of its own.
val is_null (#t: Type) (x: t) : bool
