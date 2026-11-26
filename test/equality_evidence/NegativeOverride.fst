module NegativeOverride

open Class_OverrideKey
module E = Pulse.Lib.CSharp.EqualityModel

// Must fail: an override is not given reference-identity default evidence.
let incorrect (x: class_OverrideKey__opt)
  : Lemma (E.default_equals x x)
  = ()
