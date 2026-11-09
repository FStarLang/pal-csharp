// EXPECT: PALCS0001
using PalLang;

public static class CheckedNarrowing
{
    [Requires("x == 256")]
    [Ensures("Result == 0")]
    public static byte Wrong(int x) => checked((byte)x);
}
