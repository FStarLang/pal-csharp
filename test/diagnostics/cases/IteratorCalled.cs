// EXPECT: PALCS0711
using System.Collections.Generic;
using PalLang;

public static class IteratorCalled
{
    public static IEnumerable<int> Upto(int n)
    {
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i);
            Pal.Decreases(n - i);
            yield return i;
            i++;
        }
    }

    public static void Client()
    {
        Upto(3);
    }
}
