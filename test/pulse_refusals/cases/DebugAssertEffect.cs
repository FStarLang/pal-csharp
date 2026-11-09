// EXPECT-PULSE: I32.v var_x == 1
using PalLang;
using System.Diagnostics;

public static class DebugAssertEffect
{
    [Requires("x == 0")]
    [Ensures("Result == 1")]
    public static int Wrong(int x)
    {
        Debug.Assert(++x == 1);
        // MARKER
        return x;
    }
}
