// EXPECT-PULSE: ==> I32.v __vi
// R5.6. The third loop obligation, and the one that catches people out. This invariant is
// established and is preserved; it is simply not strong enough. All that survives the loop
// is the invariant conjoined with the negated guard -- `0 <= i` and `i >= n` -- and that
// does not give `i == n`. The loop is fine; the postcondition is unreachable from what the
// author chose to remember about it.
using PalLang;

public static class InvariantTooWeak
{
    [Requires("n >= 0 && n < 1000")]
    [Ensures("Result == n")]
    public static int CountTo(int n)
    {
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i);
            Pal.Decreases(n - i);
            i++;
        }
        // MARKER
        return i;
    }
}
