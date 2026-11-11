// EXPECT: PALCS0629
// R21.5b. A binding whose documentation-comment ID names nothing. `Rat` is a typo for
// `Rate`, and the library is not referenced besides; either way nothing is bound, and the
// mistake is reported here rather than as a refused call wherever `Rate` is used.
using PalLang;

[assembly: SpecBinding("M:Acme.Sdk.Tiers.Rat(System.Int32)", "AcmeModel.rate_i32")]

public static class Unbound
{
    [Ensures("Result == 1")]
    public static int One() => 1;
}
