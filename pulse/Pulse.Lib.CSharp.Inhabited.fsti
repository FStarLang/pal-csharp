module Pulse.Lib.CSharp.Inhabited

/// Every C# type has a `default` value, and `new T[n]` fills the array with it.
/// `Pulse.Lib.CSharp.Array.alloc` needs that value, so it is exposed as a class.

class has_default (a:Type) = {
  default_value : a
}

instance has_default_bool : has_default bool = {
  default_value = false
}

instance has_default_int32 : has_default FStar.Int32.t = {
  default_value = FStar.Int32.int_to_t 0
}

instance has_default_int64 : has_default FStar.Int64.t = {
  default_value = FStar.Int64.int_to_t 0
}

instance has_default_uint32 : has_default FStar.UInt32.t = {
  default_value = FStar.UInt32.uint_to_t 0
}

instance has_default_uint64 : has_default FStar.UInt64.t = {
  default_value = FStar.UInt64.uint_to_t 0
}

instance has_default_uint8 : has_default FStar.UInt8.t = {
  default_value = 0uy
}

instance has_default_uint16 : has_default FStar.UInt16.t = {
  default_value = 0us
}

instance has_default_int16 : has_default FStar.Int16.t = {
  default_value = FStar.Int16.int_to_t 0
}

instance has_default_int8 : has_default FStar.Int8.t = {
  default_value = FStar.Int8.int_to_t 0
}

instance has_default_sizet : has_default FStar.SizeT.t = {
  default_value = 0sz
}

instance has_default_pair (a b : Type) {| has_default a |} {| has_default b |}
  : has_default (a & b) = {
  default_value = (default_value, default_value)
}

// R14.2a. `default` at a nullable type -- a class reference, `T?` -- is null, which is
// `None` wherever the type is an `option`.
instance has_default_option (a: Type) : has_default (option a) = {
  default_value = None
}

// R14.2a. `default(T)`, with `T` applied explicitly as R14.5 applies every type argument.
let default_of (a: Type) {| d: has_default a |} : a = d.default_value

// R27.35. A pointer into a region, as a type argument (`Stack<Node>`), is a nullable box,
// and its default is null.
instance has_default_box (a: Type0) : has_default (Pulse.Lib.Box.box a) = {
  default_value = Pulse.Lib.Box.null #a
}
