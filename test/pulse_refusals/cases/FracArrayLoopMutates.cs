// EXPECT-PULSE: A.pts_to
using PalLang;

public static class FracArrayLoopMutates
{
    [Requires("a.Length > 0")]
    public static void Write(int[] a)
    {
        a[0] = 1;
    }

    [Requires("a.Length > 0")]
    public static void Loop([Frac("p")] int[] a)
    {
        int i = 0;
        // MARKER
        while (i < 1)
        {
            Pal.Invariant(0 <= i && i <= 1);
            Pal.Invariant(a.Length > 0);
            Pal.Decreases(1 - i);
            Write(a);
            i++;
        }
    }
}
