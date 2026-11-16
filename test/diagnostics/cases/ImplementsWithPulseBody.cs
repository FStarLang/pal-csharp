// EXPECT: PALCS0503
// R20.14. `[Implements]` is the method's translation; a `[PulseBody]` would be a second one.
using PalLang;

public static class ImplementsWithPulseBody
{
    [Ensures("Result == x")]
    [Implements("Some.f $(x)")]
    [PulseBody("var_x")]
    public static int Ambiguous(int x) => x;
}
