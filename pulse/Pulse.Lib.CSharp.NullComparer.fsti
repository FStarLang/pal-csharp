module Pulse.Lib.CSharp.NullComparer

module O = Pulse.Lib.CSharp.Order
module N = Pulse.Lib.CSharp.Null

/// MODELING AXIOM (R27.2). `IComparer<T>` is a reference type, so `null` is one of its
/// values: `default` at a comparer type is that value, and `is_null` holds of it. This is
/// the only inhabitant of `O.comparer t` the model names that does not come from C#.
val null_comparer (#t: Type) : c: O.comparer t { N.is_null c }
