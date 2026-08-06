// EXPECT: PALCS0584
// The file's `module` header disagrees with its base name, so the emitted module would
// not be the one F* looks for.
using PalLang;

[assembly: IncludePulseFile("BadPulseModuleName.fst")]

public static class BadPulseModuleName
{
    [Ensures("return == x")]
    public static int Id(int x) => x;
}
