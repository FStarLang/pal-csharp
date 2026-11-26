module Pulse.Lib.CSharp.EqualityModel

/// Constructive comparer representation, over the existing opaque runtime model.
///
/// The two handle constructors denote disjoint runtime object categories. Only
/// EqualityComparer<C>.Default for a compiler-certified reference-identity class C
/// is represented by ReferenceDefault. In particular this is NOT a provenance
/// wrapper that may be added or removed by a cast. Every cast preserves the entire
/// handle. A default object received through a parameter must have the same
/// representation as that object obtained through EqualityComparer<C>.Default.
///
/// String comparers stay OpaqueHandle objects. Their transformations retain the
/// original runtime identity tokens, equality, and hash model; no transformation
/// is replaced by an identity operation on this category.
///
/// This module adds no axioms. Public Equality includes this model; Bcl's default
/// equality and generic code use the same semantic evidence.

module Raw = Pulse.Lib.CSharp.EqualityOpaque
module Obj = Pulse.Lib.CSharp.Obj
module SC = Pulse.Lib.CSharp.StringComparersOpaque
module SU = Pulse.Lib.CSharp.StringUnderlyingOpaque
module SCO = Pulse.Lib.CSharp.StringComparerOfOpaque
module B = Pulse.Lib.Box
module RefEq = Pulse.Lib.CSharp.RefEq

/// Restrict interpretations to the existing opaque semantics or actual identity.
/// A general user-chosen equivalence/hash dictionary is not enough to transport
/// a transformed comparer's hash law.
noeq type interpretation (t: Type0) =
  | OpaqueInterpretation : interpretation t
  | IdentityInterpretation :
      identity:(x:t -> y:t -> Tot (b:bool { b <==> x == y })) ->
      interpretation t

class has_equality (t: Type0) = {
  interpretation_of: interpretation t;
}

let opaque_equality (t: Type0) : has_equality t =
  { interpretation_of = OpaqueInterpretation }

/// Deliberately not a global instance for boxes. Nominal source-type evidence,
/// not the box storage representation, must authorize this choice.
let reference_equality (a: Type0) : has_equality (B.box a) =
  { interpretation_of = IdentityInterpretation RefEq.ref_eq }

type handle =
  | OpaqueHandle : token:Raw.handle -> handle
  | ReferenceDefault : token:Raw.handle -> handle

let comparer (_t: Type0) : eqtype = handle

let token (c: handle) : Raw.handle =
  match c with
  | OpaqueHandle h -> h
  | ReferenceDefault h -> h

let default_comparer (t: Type0) {| d: has_equality t |} : handle =
  match d.interpretation_of with
  | OpaqueInterpretation -> OpaqueHandle (Raw.default_comparer t)
  | IdentityInterpretation _ -> ReferenceDefault (Raw.default_comparer t)

[@@"opaque_to_smt"]
let equals (#t: Type0) {| d: has_equality t |}
           (c: handle) (x y: t) : bool =
  match c, d.interpretation_of with
  | ReferenceDefault _, IdentityInterpretation identity -> identity x y
  | _ -> Raw.equals (token c) x y

let equals_definition (#t: Type0) {| d: has_equality t |}
                      (c: handle) (x y: t)
  : Lemma (equals c x y ==
      (match c, d.interpretation_of with
       | ReferenceDefault _, IdentityInterpretation identity -> identity x y
       | _ -> Raw.equals (token c) x y))
  = reveal_opaque (`%equals) (equals #t #d)

let default_equals (#t: Type0) {| d: has_equality t |}
                   (x y: t) : bool =
  match d.interpretation_of with
  | OpaqueInterpretation -> Raw.default_equals x y
  | IdentityInterpretation identity -> identity x y

let default_equals_def (#t: Type0) {| d: has_equality t |} (x y: t)
  : Lemma (equals (default_comparer t) x y == default_equals x y)
          [SMTPat (equals (default_comparer t) x y)]
  = equals_definition (default_comparer t) x y;
    match d.interpretation_of with
    | OpaqueInterpretation -> Raw.default_equals_def x y
    | IdentityInterpretation _ -> ()

let get_hash_code (#t: Type0) (c: handle) (x: t) : FStar.Int32.t =
  Raw.get_hash_code (token c) x

let is_null (#t: Type0) (x: t) : bool = Raw.is_null x

let hash (#t: Type0) (c: handle) (x: t) : FStar.Int32.t =
  Raw.hash (token c) x

let equals_hash (#t: Type0) {| d: has_equality t |}
                (c: handle) (x y: t)
  : Lemma (requires equals c x y)
          (ensures hash c x == hash c y)
  = equals_definition c x y;
    match c, d.interpretation_of with
    | ReferenceDefault _, IdentityInterpretation _ -> ()
    | _ -> Raw.equals_hash (token c) x y

let object_get_hash_code (#t: Type0) {| d: has_equality t |}
                         (x: t) : FStar.Int32.t =
  hash (default_comparer t) x

/// Type identity carries the same canonical interpretation category as the
/// generic evidence. A certified plain reference-identity class cannot be string
/// or a value type. Opaque types retain the old unconstrained observations.
type type_handle =
  | OpaqueType : token:Raw.type_handle -> type_handle
  | ReferenceIdentityType : token:Raw.type_handle -> type_handle

let type_of (t: Type0) {| d: has_equality t |} : type_handle =
  match d.interpretation_of with
  | OpaqueInterpretation -> OpaqueType (Raw.type_of t)
  | IdentityInterpretation _ -> ReferenceIdentityType (Raw.type_of t)

let is_value_type (ty: type_handle) : bool =
  match ty with
  | OpaqueType h -> Raw.is_value_type h
  | ReferenceIdentityType _ -> false

/// A boxing binding must erase the model's category tag, not box the F* sum
/// representation as though it were the runtime object. Nullable and nonnullable
/// comparer boxing use the same token through Obj.box_some.
let box (c: handle) : Obj.obj = Obj.box (token c)

let box_optional (c: option handle) : Obj.obj =
  match c with
  | None -> Obj.box #(option Raw.handle) None
  | Some h -> box h

let is_non_randomized (c: handle) : bool =
  match c with
  | OpaqueHandle h -> SC.is_non_randomized h
  | ReferenceDefault _ -> false

/// A deterministic mathematical witness preserving the old opaque operation.
/// The public runtime factory exposes only a checked relational Pulse interface,
/// not this witness's deterministic result identity.
let randomized (c: handle{is_non_randomized c}) : handle =
  match c with
  | OpaqueHandle h -> OpaqueHandle (SC.randomized h)
  | ReferenceDefault _ -> c

let randomized_equals (#t: Type0) {| d: has_equality t |}
                      (c: handle{is_non_randomized c}) (x y: t)
  : Lemma (equals (randomized c) x y == equals c x y)
  = equals_definition c x y;
    equals_definition (randomized c) x y;
    match c with
    | OpaqueHandle h -> SC.randomized_equals h x y
    | ReferenceDefault _ -> ()

let non_randomized_refl (#t: Type0) {| d: has_equality t |}
                       (c: handle) (x: t)
  : Lemma (requires is_non_randomized c) (ensures equals c x x)
  = equals_definition c x x;
    match c with
    | OpaqueHandle h -> SC.non_randomized_refl h x
    | ReferenceDefault _ -> ()

/// ReferenceDefault objects do not implement IInternalStringEqualityComparer.
/// All opaque objects retain the old operation and the identity it returns.
let underlying (c: handle) : handle =
  match c with
  | OpaqueHandle h -> OpaqueHandle (SU.underlying h)
  | ReferenceDefault _ -> c

let underlying_equals (#t: Type0) {| d: has_equality t |}
                      (c: handle) (x y: t)
  : Lemma (equals (underlying c) x y == equals c x y)
  = equals_definition c x y;
    equals_definition (underlying c) x y;
    match c with
    | OpaqueHandle h -> SU.underlying_equals h x y
    | ReferenceDefault _ -> ()

let string_comparer (o: Obj.obj) : option handle =
  match SCO.string_comparer o with
  | None -> None
  | Some h -> Some (OpaqueHandle h)

let string_comparer_equals (#t: Type0) {| d: has_equality t |}
                           (c h: handle) (x y: t)
  : Lemma
      (requires
        type_of t == type_of string #(opaque_equality string) /\
        string_comparer (box_optional (Some c)) == Some h)
      (ensures is_non_randomized h /\ equals h x y == equals c x y)
  = equals_definition c x y;
    equals_definition h x y;
    match d.interpretation_of with
    | IdentityInterpretation _ -> ()
    | OpaqueInterpretation ->
      Obj.box_some (token c);
      match SCO.string_comparer (Obj.box (token c)) with
      | None -> ()
      | Some h' -> SCO.string_comparer_equals (token c) h' x y

let string_not_value_type (t: Type0) {| d: has_equality t |}
  : Lemma
      (requires type_of t == type_of string #(opaque_equality string))
      (ensures not (is_value_type (type_of t)))
  = match d.interpretation_of with
    | IdentityInterpretation _ -> ()
    | OpaqueInterpretation -> SU.string_not_value_type t

/// Focused positive controls: same-reference, distinct-reference, and null
/// equality are consequences of the chosen interpretation, not new assumptions.
let reference_default_equals (#a: Type0) (x y: B.box a)
  : Lemma
      (equals #(B.box a) #(reference_equality a)
        (default_comparer (B.box a) #(reference_equality a)) x y <==> x == y)
  = ()

/// Negative/control boundary: custom comparers remain opaque even when their
/// element type has a certified reference-identity default.
let custom_reference_equals (#a: Type0) (h: Raw.handle) (x y: B.box a)
  : Lemma
      (equals #(B.box a) #(reference_equality a) (OpaqueHandle h) x y ==
       Raw.equals h x y)
  = equals_definition #(B.box a) #(reference_equality a) (OpaqueHandle h) x y

/// Changing a string comparer's runtime identity is not collapsed to identity.
let underlying_identity (h: Raw.handle)
  : Lemma
      (underlying (OpaqueHandle h) == OpaqueHandle h <==>
       SU.underlying h == h)
  = ()

// Concrete representations with intentionally opaque default behavior.
// There is no polymorphic fallback instance: a generic definition must bind and
// preserve its caller's evidence rather than resolve opaque equality early.
instance equality_bool : has_equality bool = opaque_equality bool
instance equality_int : has_equality int = opaque_equality int
instance equality_unit : has_equality unit = opaque_equality unit
instance equality_string : has_equality string = opaque_equality string
instance equality_decimal : has_equality Pulse.Lib.CSharp.Decimal.decimal =
  opaque_equality Pulse.Lib.CSharp.Decimal.decimal
instance equality_char : has_equality FStar.Char.char = opaque_equality FStar.Char.char
instance equality_int8 : has_equality FStar.Int8.t = opaque_equality FStar.Int8.t
instance equality_int16 : has_equality FStar.Int16.t = opaque_equality FStar.Int16.t
instance equality_int32 : has_equality FStar.Int32.t = opaque_equality FStar.Int32.t
instance equality_int64 : has_equality FStar.Int64.t = opaque_equality FStar.Int64.t
instance equality_uint8 : has_equality FStar.UInt8.t = opaque_equality FStar.UInt8.t
instance equality_uint16 : has_equality FStar.UInt16.t = opaque_equality FStar.UInt16.t
instance equality_uint32 : has_equality FStar.UInt32.t = opaque_equality FStar.UInt32.t
instance equality_uint64 : has_equality FStar.UInt64.t = opaque_equality FStar.UInt64.t
instance equality_sizet : has_equality FStar.SizeT.t = opaque_equality FStar.SizeT.t
instance equality_handle : has_equality handle = opaque_equality handle
instance equality_type_handle : has_equality type_handle = opaque_equality type_handle
instance equality_obj : has_equality Obj.obj = opaque_equality Obj.obj
instance equality_option (a: Type0) : has_equality (option a) = opaque_equality (option a)
instance equality_pair (a b: Type0) : has_equality (a & b) = opaque_equality (a & b)
instance equality_list (a: Type0) : has_equality (list a) = opaque_equality (list a)
instance equality_seq (a: Type0) : has_equality (FStar.Seq.seq a) =
  opaque_equality (FStar.Seq.seq a)
