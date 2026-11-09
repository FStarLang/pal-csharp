// EXPECT: PALCS0001
using PalLang;
using System.Diagnostics;

public static class DebugAssertEffect
{
    [Requires("x == 0")]
    [Ensures("x == 1")]
    public static void Wrong(ref int x)
    {
        Debug.Assert(++x == 1);
    }
}
