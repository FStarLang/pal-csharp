module EvidenceTests

open Class_IdentityKey
open Class_OverrideKey
open Class_EquatableKey

module E = Pulse.Lib.CSharp.EqualityModel
module Raw = Pulse.Lib.CSharp.EqualityOpaque
module B = Pulse.Lib.Box

let nested_storage (#t: Type0) {| d: E.has_equality t |}
    (x: Class_EvidenceStorage.class_EvidenceStorage t #d)
  : Tot (r: Struct_NestedEvidenceStorage.struct_NestedEvidenceStorage t #d {
      FStar.Seq.equal r.Struct_NestedEvidenceStorage.fld_Owner.Struct_EvidenceEnvelope.fld_Value
        (FStar.Seq.snoc FStar.Seq.empty x) })
  = { Struct_NestedEvidenceStorage.fld_Owner = {
      Struct_EvidenceEnvelope.fld_Value = FStar.Seq.snoc FStar.Seq.empty x } }

// These use the instances emitted from the C# declarations, not manually supplied
// reference dictionaries.
let same_reference (x: class_IdentityKey__opt)
  : Lemma (E.equals (E.default_comparer class_IdentityKey__opt) x x)
  = E.reference_default_equals x x

let distinct_references (x y: class_IdentityKey__opt)
  : Lemma
      (requires ~(x == y))
      (ensures not (E.equals (E.default_comparer class_IdentityKey__opt) x y))
  = E.reference_default_equals x y

let null_reference ()
  : Lemma
      (E.default_equals (B.null #class_IdentityKey__raw)
                        (B.null #class_IdentityKey__raw))
  = ()

let unknown_override (x y: class_OverrideKey__opt)
  : Lemma
      (E.equals (E.default_comparer class_OverrideKey__opt) x y ==
       Raw.equals (Raw.default_comparer class_OverrideKey__opt) x y)
  = E.equals_definition (E.default_comparer class_OverrideKey__opt) x y

let unknown_equatable (x y: class_EquatableKey__opt)
  : Lemma
      (E.equals (E.default_comparer class_EquatableKey__opt) x y ==
       Raw.equals (Raw.default_comparer class_EquatableKey__opt) x y)
  = E.equals_definition (E.default_comparer class_EquatableKey__opt) x y

// A custom comparer is not silently given reference equality just because its
// key type has a reference-identity default.
let custom_comparer (h: Raw.handle) (x y: class_IdentityKey__opt)
  : Lemma (E.equals (E.OpaqueHandle h) x y == Raw.equals h x y)
  = E.equals_definition (E.OpaqueHandle h) x y

// Generic evidence must stay an argument; specializing this definition to the
// opaque dictionary would lose the next client's property.
let generic_default (t: Type0) {| E.has_equality t |} (x y: t) : bool =
  E.equals (E.default_comparer t) x y

let generic_reference_client (x: class_IdentityKey__opt)
  : Lemma (generic_default class_IdentityKey__opt x x)
  = E.reference_default_equals x x

// The type parameter is not part of a comparer's cast representation.
let comparer_cast (t u: Type0) (c: E.comparer t) : E.comparer u = c

let comparer_cast_identity (t u: Type0) (c: E.comparer t)
  : Lemma (comparer_cast t u c == c)
  = ()
