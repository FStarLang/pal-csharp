using System;
using System.Collections.Generic;
using PalLang;

// §20, R20.7, R20.12, R20.13. An SDK-style attribute bag in the shape of a CRM `Entity`: a
// library reference type modelled as an F* value, read through a generic accessor, written
// through its indexer, and checked by the receiver-free methods of a class that holds
// configuration in `readonly` fields.
[assembly: TranslateAnnotatedOnly]
[assembly: IncludePulse("Bag", """
module Bag
module I32 = FStar.Int32
module Inh = Pulse.Lib.CSharp.Inhabited

type value = | VInt of I32.t | VFlag of bool

noeq type bag = { attrs: option string -> option value }

let has (b: bag) (k: option string) : bool = Some? (b.attrs k)
let get (b: bag) (k: option string) : option value = b.attrs k
let put (b: bag) (k: option string) (v: option value) : option bag =
  Some { attrs = (fun k' -> if k' = k then v else b.attrs k') }

let of_bool (f: bool) : option value = Some (VFlag f)

/// The value stored at `k`, at type `t`; that it has that type is assumed.
assume val get_as (t: Type0) (b: bag) (k: option string) : t

let lookup (t: Type0) {| Inh.has_default t |} (b: option bag) (k: option string) : t =
  match b with
  | Some b -> if has b k then get_as t b k else Inh.default_of t
  | None -> Inh.default_of t

let flagged (b: option bag) (f: bool) : option bag =
  match b with Some b -> put b (Some "flag") (of_bool f) | None -> None

type tag = { tag_id: I32.t }
let tag_id (t: tag) : I32.t = t.tag_id
let new_tag (i: I32.t) : option tag = Some { tag_id = i }

let small (limit: option I32.t) (allowed: Pulse.Lib.CSharp.Bcl.hash_set I32.t) (k: option I32.t) : bool =
  match limit, k with
  | Some limit, Some k -> I32.v k < I32.v limit && Pulse.Lib.CSharp.Bcl.hash_set_contains allowed k
  | _ -> false
""")]

[SpecType("Bag.value", Nullable = true)]
public sealed class Value
{
    // R20.13: a user-defined conversion with a model.
    [SpecOp("Bag.of_bool")] public static implicit operator Value(bool f) => throw new NotImplementedException();
}

[SpecType("Bag.bag", Nullable = true)]
public sealed class Record
{
    [SpecOp("Bag.has")] public bool Contains(string key) => throw new NotImplementedException();
    // R20.7: a generic member; its type argument is passed to the model.
    [SpecOp("Bag.get_as")] public T GetAs<T>(string key) => throw new NotImplementedException();
    // R20.7 and R20.13: the indexer's getter and setter are each modelled.
    public Value this[string key]
    {
        [SpecOp("Bag.get")] get => throw new NotImplementedException();
        [SpecOp("Bag.put")] set => throw new NotImplementedException();
    }

    [SpecOp("Bag.lookup")] public static T Lookup<T>(Record r, string key) => throw new NotImplementedException();
    [SpecOp("Bag.flagged")] public static Record Flagged(Record r, bool f) => throw new NotImplementedException();
    [SpecOp("Bag.small")] public static bool Small(int? limit, HashSet<int> allowed, int? k) => throw new NotImplementedException();
}

[SpecType("Bag.tag", Nullable = true)]
public sealed class Tag
{
    // R20.13: a constructor with a model.
    [SpecOp("Bag.new_tag")] public Tag(int id) { Id = id; }
    [SpecOp("Bag.tag_id")] public int Id { get; }
}

public sealed class Checker
{
    private static readonly HashSet<int> Allowed = new HashSet<int> { 1, 2, 3 };
    private readonly int limit;

    public Checker(int limit) { this.limit = limit; }

    // R20.7: `default(T)` and a generic call, specified by a generic model.
    [Ensures("Pal.Same(Result, Record.Lookup<T>(r, key))")]
    private static T Read<T>(Record r, string key) =>
        r != null && r.Contains(key) ? r.GetAs<T>(key) : default(T);

    [Ensures("Result == Record.Lookup<int?>(r, \"size\")")]
    private static int? Size(Record r) => Read<int?>(r, "size");

    // R20.13: `r` is written through the indexer, so it is passed by reference, and the
    // implicit conversion from `bool` is `Bag.of_bool`.
    [Requires("r != null")]
    [Ensures("Pal.Same(r, Record.Flagged(Old(r), f))")]
    private static void Flag(Record r, bool f)
    {
        r["flag"] = f;
    }

    // R20.13: passing `r` on to a written parameter writes it here too.
    [Requires("r != null")]
    [Ensures("Pal.Same(r, Record.Flagged(Old(r), true))")]
    private static void FlagOn(Record r)
    {
        Flag(r, true);
    }

    [Ensures("Result != null && Result.Id == id")]
    private static Tag MakeTag(int id) => new Tag(id);

    // R20.12: a receiver-free method reads the `readonly` field `limit` and the static
    // `Allowed`, each bound as a parameter, and its contract names both.
    [Ensures("Result == Record.Small(limit, Allowed, k)")]
    private bool Accepts(int k) => k < limit && Allowed.Contains(k);

    [Ensures("Result == Record.Small(limit, Allowed, k)")]
    private bool AcceptsAgain(int k)
    {
        bool ok = Accepts(k);
        return ok;
    }
}
