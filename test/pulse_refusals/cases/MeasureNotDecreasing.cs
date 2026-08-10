// EXPECT-PULSE: << meas
// R5.9. Termination. `Pal.Decreases` names the measure, and the obligation is that the body
// lowers it; this body raises it. The loop does terminate -- the guard sees to that -- but
// the measure offered as the reason is the wrong one, and a proof of termination is a proof
// about the measure the author supplied, not about the one they had in mind.
using PalLang;

public static class MeasureNotDecreasing
{
    [Requires("n >= 0 && n < 1000")]
    public static int CountUp(int n)
    {
        int i = 0;
        // MARKER
        while (i < n)
        {
            Pal.Invariant(0 <= i && i <= n);
            Pal.Decreases(i);
            i++;
        }
        return i;
    }
}
