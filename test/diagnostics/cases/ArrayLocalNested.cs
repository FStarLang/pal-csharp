// EXPECT: PALCS0623
using PalLang;

public static class ArrayLocalNested
{
    public static int Bad(bool c)
    {
        int n = 0;
        if (c)
        {
            int[] b = new int[2];
            n = b.Length;
        }
        return n;
    }
}
