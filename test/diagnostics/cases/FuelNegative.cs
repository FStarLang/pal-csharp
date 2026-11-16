// EXPECT: PALCS0757
// R30.44. `[Fuel]`'s initial fuel and ifuel are unfolding counts; a negative one is refused.
using PalLang;

public static class Arith
{
    [Fuel(-1, 0)]
    [Ensures("Result == x")]
    public static int Id(int x) => x;
}
