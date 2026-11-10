using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R27.58. Pairs ordered by their keys: <c>SortedDictionary&lt;K, V&gt;</c>'s
/// <c>KeyValuePairComparer</c> and the map a set of such pairs is.
/// <c>Pulse.Lib.CSharp.KeyComparer</c> (trusted) and <c>Pulse.Lib.CSharp.KeyMap</c>.
/// </summary>
public static class SpecKeyMap
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecKeyMap is a specification-only construct and has no runtime meaning.");

    /// <summary>The pair comparer that compares keys by <paramref name="keyComparer"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.KeyComparer.of_keys")]
    public static IComparer<KeyValuePair<TKey, TValue>> OfKeys<TKey, TValue>(IComparer<TKey> keyComparer) =>
        throw Ghost();

    /// <summary>The key comparer of a pair comparer <see cref="OfKeys"/> built.</summary>
    [SpecOp("Pulse.Lib.CSharp.KeyComparer.key_of")]
    public static IComparer<TKey> KeyOf<TKey, TValue>(IComparer<KeyValuePair<TKey, TValue>> comparer) =>
        throw Ghost();

    /// <summary>The keys of <paramref name="pairs"/>, in order.</summary>
    [SpecOp("Pulse.Lib.CSharp.KeyMap.keys")]
    public static Seq<TKey> Keys<TKey, TValue>(Seq<KeyValuePair<TKey, TValue>> pairs) => throw Ghost();

    /// <summary>R32.11. The values of <paramref name="pairs"/>, in key order.</summary>
    [SpecOp("Pulse.Lib.CSharp.KeyMap.values")]
    public static Seq<TValue> Values<TKey, TValue>(Seq<KeyValuePair<TKey, TValue>> pairs) => throw Ghost();

    /// <summary>R34.22. The pairs of <paramref name="keys"/> and <paramref name="values"/>, position by position.</summary>
    [SpecOp("Pulse.Lib.CSharp.SortPairs.zip")]
    public static Seq<KeyValuePair<TKey, TValue>> Zip<TKey, TValue>(Seq<TKey> keys, Seq<TValue> values) => throw Ghost();

    /// <summary>R34.22. No two keys of <paramref name="pairs"/> are equivalent under <paramref name="keyComparer"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SortPairs.distinct_keys")]
    public static bool DistinctKeys<TKey, TValue>(IComparer<TKey> keyComparer, Seq<KeyValuePair<TKey, TValue>> pairs) =>
        throw Ghost();

    /// <summary>
    /// R32.11. The protocol of a walk's callback copying the key of each pair it is called
    /// on into an array from <paramref name="i0"/>, starting from contents
    /// <paramref name="a0"/>, its cursor now at <paramref name="idx"/>
    /// (<c>Pulse.Lib.CSharp.PairWalk</c>).
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.PairWalk.copied_keys")]
    public static bool CopiedKeys<TKey, TValue, X>(Seq<((KeyValuePair<TKey, TValue>, X), bool)> tr,
        Seq<TKey> a0, Seq<TKey> a, SpecInt i0, SpecInt idx) => throw Ghost();

    /// <summary>R32.11. <see cref="CopiedKeys"/> for the values.</summary>
    [SpecOp("Pulse.Lib.CSharp.PairWalk.copied_values")]
    public static bool CopiedValues<TKey, TValue, X>(Seq<((KeyValuePair<TKey, TValue>, X), bool)> tr,
        Seq<TValue> a0, Seq<TValue> a, SpecInt i0, SpecInt idx) => throw Ghost();
}
