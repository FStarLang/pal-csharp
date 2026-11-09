// EXPECT-PULSE: not (var_x = var_y)
using PalLang;

public static class BooleanXorAsOr
{
    [Ensures("Result == (x || y)")]
    public static bool Wrong(bool x, bool y)
    {
        // MARKER
        return x ^ y;
    }
}
