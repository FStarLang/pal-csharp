// EXPECT: PALCS0880
// R35.13. `Pal.Raised()` names how a `try`'s body was left, so outside a `try`'s
// invariant it has no meaning.
using PalLang;

public static class Flags
{
    [Ensures("Result == Pal.Raised()")]
    public static bool Get() => false;
}
