// EXPECT-PULSE: I32.add __vtotal
// R5.6. The other half of the loop rule. This invariant holds on entry -- `total` really is
// zero there -- and the body then adds to it, so the invariant is false at the bottom of
// the iteration. Establishment and preservation are separate obligations and a suite that
// only tests one of them tests half the rule.
using PalLang;

public static class InvariantNotPreserved
{
    [Requires("n >= 0 && n < 1000")]
    public static int Count(int n)
    {
        int i = 0;
        int total = 0;
        // MARKER
        while (i < n)
        {
            Pal.Invariant(0 <= i && i <= n);
            Pal.Invariant(total == 0);
            Pal.Decreases(n - i);
            total = total + 1;
            i++;
        }
        return total;
    }
}
