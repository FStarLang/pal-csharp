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
}
