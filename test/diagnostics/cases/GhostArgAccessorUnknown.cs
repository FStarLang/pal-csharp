// EXPECT: PALCS0885
using PalLang;
public static class GhostArgAccessorUnknown
{
    public static void Read() { Pal.Assert(Pal.Ghost<bool>("missing")); }
}
