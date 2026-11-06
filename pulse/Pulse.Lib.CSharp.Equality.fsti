module Pulse.Lib.CSharp.Equality

/// Equality comparers, as the hashing collections use them (doc/translation.md §24).
/// Every `val` here is a MODELING AXIOM (doc/translation.md R24.13, What is trusted).
///
/// An `IEqualityComparer<T>` is an object reference, a `handle`. Its type argument is
/// not part of its identity: `comparer t` is `handle` at every `t`, so that the casts
/// `(IEqualityComparer<T>)c` the BCL makes between `IEqualityComparer<string>` and
/// `IEqualityComparer<T>` (when it knows that `T` is `string`) are the identity.

val handle : eqtype

let comparer (t: Type0) : eqtype = handle

/// `c.Equals(x, y)`: a function -- deterministic, terminating, without effects.
val equals (#t: Type0) (c: handle) (x y: t) : bool

/// `c.GetHashCode(x)` for a non-null `x`.
val get_hash_code (#t: Type0) (c: handle) (x: t) : FStar.Int32.t

/// `x == null` for a value of a type parameter: R25.4's test, which is also what the
/// translator emits for `x == null` in code.
let is_null (#t: Type0) (x: t) : bool = Pulse.Lib.CSharp.Null.is_null x

/// The hash a hashing collection stores for `x`: `x != null ? c.GetHashCode(x) : 0`.
let hash (#t: Type0) (c: handle) (x: t) : FStar.Int32.t =
  if is_null x then 0l else get_hash_code c x

/// The `IEqualityComparer<T>` contract: equal values have equal hashes. This is the one
/// property of a comparer a hash table relies on to find what it stored.
val equals_hash (#t: Type0) (c: handle) (x y: t)
  : Lemma (requires equals c x y) (ensures hash c x == hash c y)

/// `EqualityComparer<T>.Default`, whose `Equals` is R22.25's `default_equals`.
val default_comparer (t: Type0) : handle

val default_equals_def (#t: Type0) (x y: t)
  : Lemma (equals (default_comparer t) x y == Pulse.Lib.CSharp.Bcl.default_equals x y)
          [SMTPat (equals (default_comparer t) x y)]

/// `x.GetHashCode()` on a value of a type parameter, which the collections call only at a
/// value type with no comparer: `EqualityComparer<T>.Default.GetHashCode(x)` is exactly
/// that call, and a `Nullable<U>` with no value hashes to 0.
let object_get_hash_code (#t: Type0) (x: t) : FStar.Int32.t = hash (default_comparer t) x

/// `System.Type`, as `typeof(T)` denotes it: compared, and asked whether it is a value type.
val type_handle : eqtype
val type_of (t: Type0) : type_handle
val is_value_type (ty: type_handle) : bool

