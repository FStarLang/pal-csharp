// EXPECT: PALCS0863
using PalLang;

public static class ArrayLocalReassigned
{
    public static int Bad(int[] a)
    {
        int[] b = new int[2];
        b = a;
        return b.Length;
    }
}
