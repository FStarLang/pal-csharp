// EXPECT: PALCS0885
using PalLang;
public static class GhostArgAccessorType
{
    [GhostArg("int witness")]
    public static void Read() { Pal.Assert(Pal.Ghost<bool>("witness")); }
}
