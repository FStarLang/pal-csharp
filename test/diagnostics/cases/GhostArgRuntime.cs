// EXPECT: PALCS0885
using PalLang;
public static class GhostArgRuntime
{
    [GhostArg("int witness")]
    public static int Read() => Pal.Ghost<int>("witness");
}
