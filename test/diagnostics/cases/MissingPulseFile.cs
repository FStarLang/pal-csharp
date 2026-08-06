// EXPECT: PALCS0583
// The named Pulse file does not exist beside this source.
using PalLang;

[assembly: IncludePulseFile("NoSuchModule.fst")]

public static class MissingPulseFile
{
    [Ensures("return == x")]
    public static int Id(int x) => x;
}
