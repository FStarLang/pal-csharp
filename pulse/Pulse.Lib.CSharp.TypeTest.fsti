module Pulse.Lib.CSharp.TypeTest

/// MODELING AXIOM (R35.7). Type tests and casts of a value at C# type `object`: the
/// `o is T`, `o is T x` and `(T)o` of a type parameter `T`, which the non-generic
/// `IDictionary`/`IList` members of the collections use to take back a key or value
/// the caller passed as `object`.
///
/// `is_a a o` is whether `o` is a non-null reference to a value of type `a`;
/// `unbox a o` is that value. Nothing is said of `unbox (box x)`: boxes are not
/// injective (Pulse.Lib.CSharp.Obj), so `unbox` returns *some* value boxing to `o`,
/// as `FStar.Dyn` does. That a type test of a box succeeds exactly when the boxed
/// value is not null, and that `object` null is the null of the value boxed, is all
/// the model knows.
///
/// Consistency: interpret `obj` as `option unit`, `box x` as `None` if `is_null x`
/// and `Some ()` otherwise, `is_null` at `obj` as `None?`, and `is_a a o` as
/// `Some? o /\ (exists (v: a). ~(is_null v))`; `unbox a o` picks such a `v`, and
/// `null_obj` is `None`. Every lemma below holds in it.
open Pulse.Lib.CSharp.Obj
module N = Pulse.Lib.CSharp.Null

val is_a (a: Type0) (o: obj) : bool

val unbox (a: Type0) (o: obj { is_a a o }) : v: a { box v == o /\ not (N.is_null v) }

val is_a_box (#a: Type0) (x: a)
  : Lemma (is_a a (box x) == not (N.is_null x)) [SMTPat (is_a a (box x))]

val is_a_not_null (a: Type0) (o: obj)
  : Lemma (requires is_a a o) (ensures not (N.is_null o)) [SMTPat (is_a a o)]

val is_null_box (#a: Type0) (x: a)
  : Lemma (N.is_null (box x) == N.is_null x) [SMTPat (N.is_null (box x))]

/// The null `object`.
val null_obj : o: obj { N.is_null o }
