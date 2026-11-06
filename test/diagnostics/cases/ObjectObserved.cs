// EXPECT: PALCS0737
// R29.4. An object is modelled as an opaque box: testing its type is refused.
using PalLang;

public static class C
{
    [Ensures("true")]
    public static bool IsInt(object o) => o is int;
}
