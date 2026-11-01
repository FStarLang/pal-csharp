using System;
using System.Collections.Generic;
using System.Text.RegularExpressions;
using PalLang;

// §20, R20.9-R20.11. Validation code in the style of a pre-nullable plugin: oblivious
// strings, choice enums cast to `int`, BCL lookups through `static readonly` fields, and
// a reference-typed SDK value read through `?.` and `??`.
[assembly: TranslateAnnotatedOnly]
[assembly: IncludePulse("Codes", """
module Codes
module I32 = FStar.Int32
module Bcl = Pulse.Lib.CSharp.Bcl

/// A choice value, which an SDK hands out as a reference that may be null.
type choice = { choice_value: I32.t }
let choice_value (c: choice) : I32.t = c.choice_value

let name_ok (s: option string) : bool =
  match s with
  | None -> false
  | Some v -> not (Bcl.is_null_or_white_space s) &&
              Bcl.is_match (Bcl.regex_create "\\A[a-z]+\\z" 8l) v

let kind_ok (k: option I32.t) : bool = k = Some 1l || k = Some 2l

let kind_of (c: option choice) : int =
  match c with None -> -1 | Some c -> I32.v (choice_value c)

let listed (c: option choice) : bool =
  match c with None -> false | Some c -> kind_ok (Some (choice_value c))
""")]

public enum Kind { None = 0, Amount = 1, UnitPrice = 2 }

[SpecType("Codes.choice", Nullable = true)]
public sealed class Choice
{
    [SpecOp("Codes.choice_value")] public int Value { get; set; }

    [SpecOp("Codes.name_ok")] public static bool NameOk(string s) => throw new InvalidOperationException();
    [SpecOp("Codes.kind_ok")] public static bool KindOk(int? k) => throw new InvalidOperationException();
    [SpecOp("Codes.kind_of")] public static int KindOf(Choice c) => throw new InvalidOperationException();
    [SpecOp("Codes.listed")] public static bool Listed(Choice c) => throw new InvalidOperationException();
}

public static class Validation
{
    private static readonly Regex NamePattern = new Regex("\\A[a-z]+\\z", RegexOptions.Compiled);
    private static readonly HashSet<int> Kinds = new HashSet<int> { (int)Kind.Amount, (int)Kind.UnitPrice };

    // R20.9: `string` is `option string`; R20.10: the BCL calls are their models.
    [Ensures("Result == Choice.NameOk(name)")]
    public static bool NameValid(string name) =>
        !string.IsNullOrWhiteSpace(name) && NamePattern.IsMatch(name);

    // R20.9: an enum constant cast to `int` is its value, and `==` on `int?` is option equality.
    [Ensures("Result == Choice.KindOk(kind)")]
    public static bool KindValid(int? kind) =>
        kind == (int)Kind.Amount || kind == (int)Kind.UnitPrice;

    // R20.10: a `HashSet` built by a collection initializer, queried.
    [Ensures("Result == Choice.KindOk(kind)")]
    public static bool KindListed(int kind) => Kinds.Contains(kind);

    // R20.11: `?.` reads through a nullable reference only when it is not null, and `??`
    // supplies the value for the null case.
    [Ensures("Result == Choice.KindOf(choice)")]
    public static int KindOfChoice(Choice choice) => choice?.Value ?? -1;

    // R20.11: `!= null` on a nullable reference; R5.2a: a `bool` local never written again
    // is a value, so what it was initialised to survives the branches after it.
    [Ensures("Result == Choice.Listed(choice)")]
    public static bool Chosen(Choice choice)
    {
        bool present = choice != null;
        if (!present)
        {
            return false;
        }
        return KindListed(choice.Value);
    }
}
