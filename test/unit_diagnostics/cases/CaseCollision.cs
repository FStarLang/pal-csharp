// EXPECT: PALCS0758
// REFERENCES: lib
using PalLang;

namespace Other;

public static class Util
{
    [Ensures("Result == x")]
    public static int id(int x)
    {
        return x;
    }
}
