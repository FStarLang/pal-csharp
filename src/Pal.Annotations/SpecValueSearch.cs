using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R32.8. A search of a map's values by a walk of its pairs (<c>SortedDictionary&lt;K, V&gt;.ContainsValue</c>).
/// <c>Pulse.Lib.CSharp.ValueSearch</c>.
/// </summary>
public static class SpecValueSearch
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecValueSearch is a specification-only construct and has no runtime meaning.");

    /// <summary>
    /// <paramref name="x"/> matches <paramref name="y"/>: it is null when <paramref name="y"/> is,
    /// and <see cref="Pal.DefaultEquals{T}"/> to it otherwise.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.ValueSearch.value_matches")]
    public static bool Matches<TValue>(TValue x, TValue y) => throw Ghost();

    /// <summary>Some pair of <paramref name="pairs"/> has a value that <see cref="Matches"/> <paramref name="value"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.ValueSearch.has_value")]
    public static bool HasValue<TKey, TValue>(Seq<KeyValuePair<TKey, TValue>> pairs, TValue value) => throw Ghost();

    /// <summary>
    /// The protocol of the search's callback (R27.39): each call returned false exactly on a
    /// match, and <paramref name="found"/> is whether one matched.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.ValueSearch.searched")]
    public static bool Searched<TKey, TValue, X>(Seq<((KeyValuePair<TKey, TValue>, X), bool)> tr, TValue value, bool found) => throw Ghost();
}
