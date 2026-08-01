// EXPECT: PALCS0503
// Two implementations, no rule for choosing between them.
using PalLang;

public static class TwoBodies
{
    [Ensures("return == x")]
    [PulseBody("!var_x")]
    public static int Ambiguous(int x) => x;
}
