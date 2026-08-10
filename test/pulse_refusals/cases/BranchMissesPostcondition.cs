// EXPECT-PULSE: I32.v (I32.sub var_x 1l) >= 0
// R5.4. A postcondition has to hold on every path, and this one holds on one. The `if` is
// where the paths part and the exit is where they join, so a case that only breaks the
// arithmetic on a straight line never asks whether the join is sound at all.
//
// The interesting half is that the *other* branch is right. `Abs` returns the correct
// answer for a negative argument and the wrong one for zero, so nothing about the method is
// uniformly broken -- which is what makes it the shape of a real mistake rather than a
// deliberately silly program.
using PalLang;

public static class BranchMissesPostcondition
{
    [Requires("x > -1000 && x < 1000")]
    [Ensures("Result >= 0 && (Result == x || Result == -x)")]
    public static int Abs(int x)
    {
        if (x < 0)
        {
            return -x;
        }

        // MARKER
        return x - 1;
    }
}
