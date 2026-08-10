// EXPECT-PULSE: < FStar.Seq.Base.length pre_a
// R6.5/R3.3. An array read carries the obligation that the index is in bounds, and nothing in
// the frontend discharges it: `a[i]` translates to `A.op_Array_Access`, whose precondition
// is that `i` is below the length. The contract here bounds `i` below and not above, so
// the obligation is exactly the missing half.
using PalLang;

public static class IndexInBounds
{
    [Requires("i >= 0")]
    public static int At(int[] a, int i)
    {
        // MARKER
        return a[i];
    }
}
