module Pulse.Lib.CSharp.Delegate

/// A delegate that verified code may *call* (doc/translation.md R26.1): `Predicate<T>`,
/// `Action<T>`, `Converter<TIn, TOut>` and `Comparison<T>`.
///
/// Every `val` here is a MODELING AXIOM (R26.12). A delegate is modelled as a pure, total
/// function of its arguments, together with whether the reference is null:
///
///  * invoking it terminates, does not throw, and touches nothing verified code owns
///    (in particular, not the collection that is calling it);
///  * it is deterministic: two calls with the same arguments return the same value.
///
/// So `apply1 f x` is both what a call `f(x)` returns and what a contract means by `f(x)`.
/// Calling a null delegate is never modelled: verified code tests `is_null1` first (the
/// BCL throws `ArgumentNullException`), and the type is otherwise abstract. The axioms are
/// consistent: `fn1 a r = bool & (a -> r)`, with `is_null1 = fst`, is a model of them.

/// A delegate of one argument.
val fn1 (a: Type0) (r: Type0) : Type0

/// A delegate of two arguments.
val fn2 (a: Type0) (b: Type0) (r: Type0) : Type0

/// `f(x)`.
val apply1 (#a #r: Type0) (f: fn1 a r) (x: a) : r

/// `f(x, y)`.
val apply2 (#a #b #r: Type0) (f: fn2 a b r) (x: a) (y: b) : r

/// `f == null`.
val is_null1 (#a #r: Type0) (f: fn1 a r) : bool

val is_null2 (#a #b #r: Type0) (f: fn2 a b r) : bool
