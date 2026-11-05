using System;
using System.Collections.Generic;
using PalLang;

// §26. Sorting with a comparer that may be null, and the capacity-threshold idiom.
public static class Sorter
{
    // R26.7. `Array.Sort` sorts the range and leaves the rest alone; `null` is the default order.
    [Requires("0 <= index && 0 <= count && index + count <= items.Length")]
    [Ensures("Pal.SortedRange(Pal.Old(Pal.Contents(items)), Pal.Contents(items), index, count, comparer)")]
    public static void SortRange<T>(T[] items, int index, int count, IComparer<T>? comparer) =>
        Array.Sort(items, index, count, comparer);

    // R26.6. `(int)(n * 0.9)`, the `int` converted implicitly...
    [Requires("0 <= n")]
    [Ensures("0 <= Result && Result <= n")]
    public static int Threshold(int n) => (int)(n * 0.9);

    // ...and by a cast.
    [Requires("0 <= n")]
    [Ensures("0 <= Result && Result <= n")]
    public static int ThresholdCast(int n) => (int)((double)n * 0.9);

    // R26.13. `is null` on a comparer is `is_null`.
    [Ensures("Result == Pal.IsNull(comparer)")]
    public static bool NoComparer<T>(IComparer<T>? comparer) => comparer is null;
}
