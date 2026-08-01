// EXPECT: PALCS0200
using PalLang;

public static class NoMeasure
{
    public static void Spin(int n)
    {
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i);
            i = i + 1;
        }
    }
}
