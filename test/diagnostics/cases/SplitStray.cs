// EXPECT: PALCS0755
// R30.39. `Pal.Split()` outlines what follows the joins of an `if`; with no join before
// it there is no contract for the outlined function.
using PalLang;

public static class Arith
{
    [Ensures("Result == x")]
    public static int Id(int x)
    {
        Pal.Split();
        return x;
    }
}
