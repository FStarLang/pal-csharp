using System.Collections.Generic;
using PalLang;

[Plain]
internal sealed class ReferenceKey
{
    internal int Value;

    internal ReferenceKey(int value) => Value = value;
}

internal static class ReferenceKeys
{
    [Ensures("!Result")]
    internal static bool Duplicate(ReferenceKey key)
    {
        var seen = new HashSet<ReferenceKey>();
        seen.Add(key);
        return seen.Add(key);
    }

    [Ensures("!Result")]
    internal static bool DuplicateAfterGrowth(ReferenceKey key)
    {
        var seen = new HashSet<ReferenceKey>();
        seen.Add(key);
        seen.EnsureCapacity(7);
        return seen.Add(key);
    }

    [Requires("first != second")]
    [Ensures("Result")]
    internal static bool Distinct(ReferenceKey first, ReferenceKey second)
    {
        var seen = new HashSet<ReferenceKey>();
        seen.Add(first);
        return seen.Add(second);
    }

    [Ensures("0 <= Result && Result <= 2")]
    internal static int InsertTwice(ReferenceKey key)
    {
        var seen = new HashSet<ReferenceKey>();
        seen.Add(key);
        seen.Add(key);
        return seen.Count;
    }
}
