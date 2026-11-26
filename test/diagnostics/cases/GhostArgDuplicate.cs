// EXPECT: PALCS0884
using PalLang;

public static class GhostArgDuplicate
{
    [GhostArg("SpecInt snapshot"), GhostArg("int snapshot")]
    public static int Read(int value) => value;
}
