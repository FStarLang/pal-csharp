// EXPECT: PALCS0902
using PalLang;

public static class AssumeIsUnsound
{
    [Ensures("return == 1")]
    public static int Cheat(int x)
    {
        Pal.Assume(x == 1);
        return x;
    }
}
