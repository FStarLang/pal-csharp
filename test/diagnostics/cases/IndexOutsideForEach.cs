// EXPECT: PALCS0621
using PalLang;

public static class IndexOutsideForEach
{
    public static void Bad(int[] a)
    {
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(Pal.Index(i) >= 0);
        }
    }
}
