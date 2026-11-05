using System;
using PalLang;

// §26. Searching an array with a caller's delegate, and leaving a loop by `return`.
[assembly: TranslateAnnotatedOnly]

public static class Finder
{
    // R26.1, R26.2, R26.3. A `Predicate<T>` invoked in a loop that returns from inside.
    [Requires("match != null")]
    [Ensures("Result == Pal.FindIndex(Pal.Contents(items), match)")]
    public static int FindIndex<T>(T[] items, Predicate<T> match)
    {
        for (int i = 0; i < items.Length; i++)
        {
            Pal.Invariant(0 <= i && i <= items.Length);
            Pal.Invariant(Pal.Forall((SpecInt k) =>
                Pal.Implies(0 <= k && k < i, !match(Pal.Contents(items)[k]))));
            Pal.Invariant(Pal.Implies(Pal.Returned(),
                Pal.ReturnValue<int>() == Pal.FindIndex(Pal.Contents(items), match)));
            if (match(items[i]))
                return i;
        }
        return -1;
    }

    // R26.1. A delegate may be null; the comparison is `is_null`.
    [Ensures("Result == (match == null)")]
    public static bool IsMissing<T>(Predicate<T> match) => match == null;
}
