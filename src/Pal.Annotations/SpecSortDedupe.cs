using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R34.27. A set built from items under a comparer, as <c>SortedSet&lt;T&gt;</c>'s
/// constructor builds it by sorting and dropping equivalent items.
/// <c>Pulse.Lib.CSharp.SortDedupe</c> (verified).
/// </summary>
public static class SpecSortDedupe
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecSortDedupe is a specification-only construct and has no runtime meaning.");

    /// <summary>
    /// <paramref name="items"/> is the set of <paramref name="source"/>'s items under
    /// <paramref name="comparer"/>: strictly sorted, every item of the source has an
    /// equivalent in it, and each of its items is an item of the source.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SortDedupe.set_of")]
    public static bool SetOf<T>(IComparer<T> comparer, Seq<T> items, Seq<T> source) => throw Ghost();

    /// <summary><paramref name="s"/>[lo, hi) is in <paramref name="comparer"/>'s order.</summary>
    [SpecOp("Pulse.Lib.CSharp.Sort.sorted_in")]
    public static bool SortedIn<T>(IComparer<T> comparer, Seq<T> s, SpecInt lo, SpecInt hi) => throw Ghost();

    /// <summary><paramref name="s"/> with item <paramref name="i"/> replaced by <paramref name="x"/>.</summary>
    [SpecOp("FStar.Seq.upd")]
    public static Seq<T> Update<T>(Seq<T> s, SpecInt i, T x) => throw Ghost();

    /// <summary>
    /// The dedupe loop's invariant after <paramref name="i"/> of <paramref name="n"/> items,
    /// <paramref name="index"/> kept (<c>Pulse.Lib.CSharp.SortDedupe.dedupe_inv</c>).
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SortDedupe.dedupe_inv")]
    public static bool DedupeInv<T>(IComparer<T> comparer, Seq<T> source, Seq<T> a, SpecInt i, SpecInt index, SpecInt n) =>
        throw Ghost();

    /// <summary>R27.47. <c>c.Equals(d)</c>, an uninterpreted, deterministic test.</summary>
    [SpecOp("Pulse.Lib.CSharp.SortDedupe.comparer_equals")]
    public static bool ComparerEquals<T>(IComparer<T> c, IComparer<T> d) => throw Ghost();
}
