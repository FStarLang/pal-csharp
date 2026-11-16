// EXPECT: PALCS0884
using PalLang;

public static class GhostArgMalformed
{
    [GhostArg("ref int snapshot")]
    public static int Read(int value) => value;
}
