// EXPECT: PALCS0622
using System.Collections.Generic;
using System.Linq;
using PalLang;

public static class UnsupportedLinq
{
    public static int Bad([Frac("p")] IList<int> xs)
    {
        var sorted = xs.OrderBy(x => -x).ToList();
        return sorted.Count;
    }
}
