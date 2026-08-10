// EXPECT-PULSE: 0 < I32.v 0l
// R5.6. A loop invariant has to hold on entry, and this one does not: `i` is zero when the
// loop is reached and the invariant claims it is positive. The obligation is discharged
// against the state *before* the first iteration, so the body -- which would maintain the
// invariant perfectly well -- never gets to matter.
using PalLang;

public static class InvariantNotEstablished
{
    public static int CountUp(int n)
    {
        int i = 0;
        // MARKER
        while (i < n)
        {
            Pal.Invariant(0 < i && i <= n);
            Pal.Decreases(n - i);
            i++;
        }
        return i;
    }
}
