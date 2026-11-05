module Pulse.Lib.CSharp.Comparer

/// The `null` comparer (doc/translation.md R26.7), over §25's comparer model
/// (`Pulse.Lib.CSharp.Order`, `Pulse.Lib.CSharp.Sorted`). MODELING AXIOM: there is a
/// comparer value that `Sorted.is_null` holds of, the `null` a program passes to a BCL
/// sort or search, which `Sorted.or_default` replaces by `Comparer<T>.Default`.

module O = Pulse.Lib.CSharp.Order

val null_comparer (t: Type) : c: O.comparer t { Pulse.Lib.CSharp.Sorted.is_null c }
