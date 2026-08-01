// EXPECT: PALCS0508
using PalLang;

public static class SpecCallsProgram
{
    public static int Double(int x) => x + x;

    [Spec]
    public static SpecInt Bad(SpecInt x) => SpecCallsProgram.Double(1);
}
