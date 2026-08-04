using System;
using PalLang;

// §11. The model type this test's recursive class uses, written in F* by the user and
// carried into the translation as its own module (§7). Nothing about it is known to the
// compiler: `SpecAssoc` below declares what each piece means, and the translator emits
// those names verbatim.
//
// The shape is deliberately neither a list nor a tree. `Entry` takes **two** pure
// arguments and one recursive one, which is an arity the old `RecursiveShape` enum could
// not name — and R11.6 says the arity was never the point.
[assembly: IncludePulse("UserAssoc", """
module UserAssoc

/// An association list: a key and a value at each node.
noeq type assoc (k: Type0) (v: Type0) =
  | Empty : assoc k v
  | Entry : k -> v -> assoc k v -> assoc k v

let rec length (#k #v: Type0) (m: assoc k v) : Tot nat (decreases m) =
  match m with
  | Empty -> 0
  | Entry _ _ tl -> 1 + length tl

/// Lookup, the model of the traversal below.
let rec find (#v: Type0) (m: assoc int v) (key: int) : Tot (option v) (decreases m) =
  match m with
  | Empty -> None
  | Entry k x tl -> if k = key then Some x else find tl key

/// The value at a key, or a default. A total function is easier to specify against than
/// an `option`, and having it here rather than in the C# file is exactly what §0 rule 3
/// prescribes: a proof that needs help gets it from the library, not from the emitter.
let get (m: assoc int int) (key: int) (dflt: int) : int =
  match find m key with
  | None -> dflt
  | Some x -> x

/// Update in place, the model of the destructive traversal below.
let rec set (m: assoc int int) (key: int) (x: int) : Tot (assoc int int) (decreases m) =
  match m with
  | Empty -> Empty
  | Entry k v tl -> if k = key then Entry k x tl else Entry k v (set tl key x)

let rec set_length (m: assoc int int) (key x: int)
  : Lemma (ensures length (set m key x) == length m) (decreases m)
          [SMTPat (length (set m key x))]
  = match m with
    | Empty -> ()
    | Entry k _ tl -> if k = key then () else set_length tl key x

/// Prepending is what the constructor does, and the fact a client needs about it.
let entry_length (#k #v: Type0) (key: k) (x: v) (tl: assoc k v)
  : Lemma (length (Entry key x tl) == 1 + length tl)
  = ()
""")]

namespace PalCSharp.Tests;

/// <summary>
/// R11.1. The C# surface of <c>UserAssoc.assoc</c>. This is the whole of what a user
/// writes to bring their own specification type: one attribute naming the F* type, and one
/// attribute per member naming the F* term it denotes.
///
/// <para>Note what is <em>not</em> here. There is no entry in a table of known types, no
/// <c>IrType</c> case, no enum of model shapes, and no branch anywhere in the translator.
/// The declaration below is the only place either name appears.</para>
/// </summary>
[SpecType("UserAssoc.assoc")]
public readonly struct SpecAssoc<K, V>
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecAssoc<K, V> is a specification-only construct and has no runtime meaning.");

    /// <summary>R11.2. A property is an application to the receiver.</summary>
    [SpecOp("UserAssoc.length")]
    public SpecInt Count => throw Ghost();

    /// <summary>
    /// R11.2. A discriminator needs no rule of its own: <c>Empty?</c> is a prefix function
    /// of one argument (F44), so it is a <c>[SpecOp]</c> like any other.
    /// </summary>
    [SpecOp("UserAssoc.Empty?")]
    public bool IsEmpty => throw Ghost();

    /// <summary>R11.2. An instance method: the receiver first, then the arguments.</summary>
    [SpecOp("UserAssoc.get")]
    public SpecInt Get(SpecInt key, SpecInt fallback) => throw Ghost();

    public static bool operator ==(SpecAssoc<K, V> a, SpecAssoc<K, V> b) => throw Ghost();
    public static bool operator !=(SpecAssoc<K, V> a, SpecAssoc<K, V> b) => throw Ghost();

    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

/// <summary>
/// R11.3. The constructors, declared together so that a use of one finds the other. Which
/// is empty is the one thing the translator cannot derive — a null reference has to denote
/// exactly one constructor, and only the user knows which.
/// </summary>
public static class SpecAssoc
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecAssoc is a specification-only construct and has no runtime meaning.");

    /// <summary>What a null reference denotes.</summary>
    [SpecCtor("UserAssoc.Empty", Empty = true)]
    public static SpecAssoc<K, V> Nil<K, V>() => throw Ghost();

    /// <summary>Two pure arguments and one recursive one (R11.6).</summary>
    [SpecCtor("UserAssoc.Entry")]
    public static SpecAssoc<K, V> Entry<K, V>(K key, V value, SpecAssoc<K, V> rest) =>
        throw Ghost();

    /// <summary>R11.2. An ordinary static operation.</summary>
    [SpecOp("UserAssoc.set")]
    public static SpecAssoc<SpecInt, SpecInt> Set(
        SpecAssoc<SpecInt, SpecInt> map, SpecInt key, SpecInt value) => throw Ghost();
}
