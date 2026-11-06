// EXPECT: PALCS0712
using System.Collections.Generic;
using PalLang;

public static class IteratorSharesReference
{
    public static IEnumerable<int> Each(int[] a)
    {
        yield return a[0];
    }
}
