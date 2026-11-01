module Pulse.Lib.CSharp.Bcl

/// Models of the few BCL members production code calls (doc/translation.md R20.10).
/// Each `val` here is a MODELING AXIOM: the translation trusts that the BCL member it
/// stands for is the function it is declared to be.

/// `System.Guid`: a value with equality, and `Guid.Empty`.
val guid : eqtype
val guid_empty : guid

/// `char.IsWhiteSpace`, left uninterpreted: the Unicode table is not modelled.
val is_white_space (c: FStar.Char.char) : bool

/// `string.IsNullOrWhiteSpace`.
let is_null_or_white_space (s: option string) : bool =
  match s with
  | None -> true
  | Some s -> FStar.List.Tot.for_all is_white_space (FStar.String.list_of_string s)

/// `string.Equals(a, b, StringComparison.Ordinal)`: ordinal equality, null equal only to null.
let string_equals_ordinal (a b: option string) : bool = a = b

/// `System.Text.RegularExpressions.Regex`: a pattern and its options, and a match
/// predicate left uninterpreted. Matching is assumed deterministic and to terminate.
val regex : Type0
val regex_create (pattern: string) (options: FStar.Int32.t) : regex
val is_match (r: regex) (input: string) : bool

/// `HashSet<T>` built by a collection initializer and only queried: its elements.
let hash_set (a: eqtype) = list a
let hash_set_empty (#a: eqtype) : hash_set a = []
let hash_set_add (#a: eqtype) (x: a) (s: hash_set a) : hash_set a = x :: s
let hash_set_contains (#a: eqtype) (s: hash_set a) (x: a) : bool = FStar.List.Tot.mem x s
