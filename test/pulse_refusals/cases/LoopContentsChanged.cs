// EXPECT-PULSE: I32.v (Seq.index
// R5.8e preserves array length, not the values overwritten by the loop.
using PalLang;

public static class LoopContentsChanged
{
    [Requires("a.Length == 1 && Contents(a)[0] == 1")]
    public static void Clear(int[] a)
    {
        for (int i = 0; i < 1; i++)
        {
            Pal.Invariant(0 <= i && i <= 1);
            a[0] = 0;
        }
        // MARKER
        Pal.Assert(Pal.Contents(a)[0] == 1);
    }
}
