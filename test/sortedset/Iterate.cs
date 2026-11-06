using System.Collections.Generic;
using PalLang;

// R27.42. Iterator methods: `yield return` extends what the method has yielded, and
// `yield break` — at the top level or inside a loop — ends the enumeration.
public static class Iterate
{
    [Requires("n >= 0 && stop >= 0")]
    [Ensures("Pal.Yielded<int>().Length == (n == 0 ? 0 : (n < stop ? n : stop))")]
    public static IEnumerable<int> Upto(int n, int stop)
    {
        if (n == 0)
        {
            yield break;
        }
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i && i <= n && i <= stop && Pal.Yielded<int>().Length == i && Pal.Implies(Pal.Returned(), i == stop));
            Pal.Decreases(n - i);
            if (i == stop)
            {
                yield break;
            }
            yield return i;
            i++;
        }
    }
}
