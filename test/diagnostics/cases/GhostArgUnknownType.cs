// EXPECT: PALCS0100
using PalLang;

public static class GhostArgUnknownType
{
    [GhostArg("NoSuchType snapshot")]
    public static int Read(int value) => value;
}
