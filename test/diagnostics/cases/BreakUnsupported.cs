// EXPECT: PALCS0001
using PalLang;

public static class BreakUnsupported
{
    public static void Bad(int n)
    {
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i);
            Pal.Decreases(n - i);
            if (i == 3) { break; }
            i = i + 1;
        }
    }
}
