// EXPECT: PALCS0001
// `goto` needs the control-flow restructuring pass PAL has and pal-csharp does not.
using PalLang;

public static class GotoUnsupported
{
    public static int Bad(int x)
    {
        int y = x;
    again:
        if (y > 0) { y = y - 1; goto again; }
        return y;
    }
}
