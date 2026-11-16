// EXPECT-PULSE: pre_a
using PalLang;

public static class OwnedArrayLoopNotFramed
{
    public static int Length([Frac("p")] int[] a) => a.Length;

    [Ensures("Contents(a) == Old(Contents(a))")]
    public static void Loop(int[] a)
    {
        int i = 0;
        while (i < 1)
        {
            Pal.Invariant(0 <= i && i <= 1);
            Pal.Decreases(1 - i);
            Length(a);
            i++;
        }
        // MARKER
        return;
    }
}
