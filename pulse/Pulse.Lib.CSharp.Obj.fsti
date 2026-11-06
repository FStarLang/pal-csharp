module Pulse.Lib.CSharp.Obj

/// A value at C# type `object`, or at one of the enumerator interfaces a collection's
/// explicit members return (doc/translation.md R29.4).
///
/// Verified code may produce such a value -- by boxing, or by seeing a reference at an
/// interface type -- return it and pass it on, and nothing else: it cannot compare it,
/// test it for null or cast it back. So the only fact about an `obj` is how it was made.
val obj : Type0

/// The conversion of `x` to `object`. Nothing is said of it: in particular it is not
/// stated to be injective, because reference identity of boxes is not a function of
/// the value boxed.
val box (#a: Type0) (x: a) : obj

/// The type of CoreLib's shared empty enumerator over `a`, `SZGenericArrayEnumerator<T>`:
/// an object like any other, which verified code only ever converts to an interface.
unfold let enumerator_of (a: Type0) : Type0 = obj

/// An enumerator over no elements, at element type `a`: what the BCL's shared empty
/// enumerators (`SZGenericArrayEnumerator<T>.Empty`, `EnumerableHelpers.GetEmptyEnumerator<T>()`)
/// are bound to. Which object it is, is left uninterpreted.
val empty_enumerator (a: Type0) : obj
