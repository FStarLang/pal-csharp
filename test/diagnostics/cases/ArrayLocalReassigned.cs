// EXPECT: PALCS0623
using PalLang;

public static class ArrayLocalReassigned
{
    public static int Bad()
    {
        int[] b = new int[2];
        b = new int[3];
        return b.Length;
    }
}
