// EXPECT: PALCS0001
using PalLang;

public static class UnsupportedThrow
{
    public static int Bad(int x)
    {
        if (x < 0) { throw new System.Exception("no"); }
        return x;
    }
}
