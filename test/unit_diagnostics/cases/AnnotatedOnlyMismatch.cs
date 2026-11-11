// EXPECT: PALCS0761
// REFERENCES: annotated
// R36.5. The referenced unit translates only its annotated members; this one translates all.
using PalLang;

public static class Whole
{
    [Ensures("Result == 1")]
    public static int One()
    {
        return PalCSharp.Tests.Picked.Same(1);
    }
}
