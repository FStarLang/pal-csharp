module Pulse.Lib.CSharp.ComparerIdentity

/// Comparer references (doc/translation.md R27.47), over §25's comparer model
/// (`Pulse.Lib.CSharp.Order`).

module O = Pulse.Lib.CSharp.Order

/// MODELING AXIOM (R27.47). A comparer value stands for the object: `==` on two
/// `IComparer<T>` references is reference equality, which is equality of their values.
/// `Comparer<T>.Default` is one cached object, and the null comparer one value, so the
/// model already gives each of those a single value. Two distinct objects that order alike
/// are distinct values; nothing states that they are not.
val same (#t: Type) (c d: O.comparer t) : b: bool { b <==> c == d }

/// MODELING AXIOM (R27.47). `c.Equals(o)`, `object.Equals` called on a comparer, which the
/// comparer's class may override: a pure, total, deterministic function, and nothing more.
/// In particular it is *not* stated that `equals c (box d)` implies that `c` and `d` order
/// alike: a class may override `Equals` to say anything.
val equals (#t: Type) (c: O.comparer t) (o: Pulse.Lib.CSharp.Obj.obj) : bool
