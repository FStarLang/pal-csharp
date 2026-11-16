// EXPECT: PALCS0756
// R30.40. `[OpaqueSpecs]` names the declaring type's `[Spec]` methods; `Twice` is not one.
using PalLang;

public static class Arith
{
    public static int Twice(int x) => x + x;

    [OpaqueSpecs("Twice")]
    [Ensures("Result == x")]
    public static int Id(int x) => x;
}
