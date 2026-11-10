// EXPECT: PALCS0881
// R35.18. A `[Specialize]` parameter is translated once per constant its callers pass, so
// every call must pass a literal (or forward the parameter of a specialization).
using PalLang;

public static class Gauge
{
    [Ensures("Result >= 0")]
    private static int Level([Specialize] bool full)
    {
        if (full) return 1;
        return 0;
    }

    [Ensures("Result >= 0")]
    public static int Touch(bool b)
    {
        return Level(b);
    }
}
