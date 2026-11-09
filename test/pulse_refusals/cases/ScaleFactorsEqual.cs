// EXPECT-PULSE: scale_unit
using PalLang;

public static class ScaleFactorsEqual
{
    [Ensures("Result")]
    public static bool Wrong(int x)
    {
        int half = (int)((double)x * 0.5);
        int threeQuarters = (int)((double)x * 0.75);
        // MARKER
        return half == threeQuarters;
    }
}
