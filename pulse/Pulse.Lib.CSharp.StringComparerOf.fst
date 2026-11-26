module Pulse.Lib.CSharp.StringComparerOf

module E = Pulse.Lib.CSharp.EqualityModel
let string_comparer = E.string_comparer
let string_comparer_equals (#t: Type0) {| E.has_equality t |}
                           (c h: E.handle) (x y: t)
  : Lemma
      (requires E.type_of t == E.type_of string /\
                string_comparer (E.box_optional (Some c)) == Some h)
      (ensures E.is_non_randomized h /\ E.equals h x y == E.equals c x y)
  = E.string_comparer_equals c h x y
