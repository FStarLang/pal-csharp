// EXPECT: PALCS0304
// A termination measure sees the live array but not its contents: the contents are the
// loop invariant's existential, which F3 forbids a measure from mentioning.
using PalLang;

public static class ArrayInMeasure
{
    public static void Bad(int[] a)
    {
        int i = 0;
        while (i < a.Length)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Decreases(a[i]);
            i = i + 1;
        }
    }
}
