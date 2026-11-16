// EXPECT: PALCS0884
using PalLang;

public static class GhostArgCollision
{
    [GhostArg("SpecInt value")]
    public static int Read(int value) => value;
}
