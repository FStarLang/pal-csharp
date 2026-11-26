module NegativeReinterpretation

module E = Pulse.Lib.CSharp.EqualityModel
module B = Pulse.Lib.Box

// Must fail: ownership at one dictionary cannot be reinterpreted at another.
// Use the compiler's actual nominal storage type, not a hand-written stand-in.
let incorrect (t: Type0) (d1 d2: E.has_equality t)
              (p: B.box (Class_EvidenceStorage.class_EvidenceStorage__raw t #d1))
  : B.box (Class_EvidenceStorage.class_EvidenceStorage__raw t #d2) =
  p
