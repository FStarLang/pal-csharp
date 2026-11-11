// EXPECT: PALCS0758
// REFERENCES: lib
// R36.4. `Other.Util.Id` is emitted as `Func_Util_Id`, which the referenced unit emits too.
using PalLang;

namespace Other;

public static class Util
{
    [Ensures("Result == x")]
    public static int Id(int x)
    {
        return x;
    }
}
