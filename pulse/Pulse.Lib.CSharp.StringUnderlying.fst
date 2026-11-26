module Pulse.Lib.CSharp.StringUnderlying

module E = Pulse.Lib.CSharp.EqualityModel
let underlying = E.underlying
let underlying_equals (#t: Type0) {| E.has_equality t |} (c: E.handle) (x y: t)
  : Lemma (E.equals (underlying c) x y == E.equals c x y)
          [SMTPat (E.equals (underlying c) x y)]
  = E.underlying_equals c x y
let string_not_value_type (t: Type0) {| E.has_equality t |}
  : Lemma (requires E.type_of t == E.type_of string)
          (ensures not (E.is_value_type (E.type_of t)))
          [SMTPat (E.is_value_type (E.type_of t))]
  = E.string_not_value_type t
