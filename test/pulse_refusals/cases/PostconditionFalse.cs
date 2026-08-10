// EXPECT-PULSE: I32.v (I32.add var_x 2l) == I32.v var_x + 1
// R4.1. The plainest negative case there is: the contract says one thing and the body
// computes another. Everything else in this directory is a variation on it, but the
// unadorned version is worth having on its own, because it is the failure a user meets
// first and the one whose message therefore matters most.
using PalLang;

public static class PostconditionFalse
{
    [Requires("x > 0 && x < 1000")]
    [Ensures("Result == x + 1")]
    public static int Increment(int x)
    {
        // MARKER
        return x + 2;
    }
}
