module NegativeEquatable

open Class_EquatableKey
module E = Pulse.Lib.CSharp.EqualityModel

// Must fail: an explicit IEquatable implementation is not reference evidence.
let incorrect (x: class_EquatableKey__opt)
  : Lemma (E.default_equals x x)
  = ()
