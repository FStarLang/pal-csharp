// EXPECT: PALCS0001
using PalLang;

public static class NamedArgumentOrder
{
    [Ensures("Result == first")]
    public static int First(int first, int second) => first;

    [Ensures("Result == 2")]
    public static int Wrong() => First(second: 2, first: 1);
}
