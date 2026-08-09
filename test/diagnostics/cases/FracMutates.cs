// EXPECT: PALCS0551
// R4.11c. `[Frac("p")]` says the caller keeps a share and is handed the object back at the
// model it arrived at. A body that assigns a field says the model moves. Both cannot be
// true, and left to run this does not fail honestly: on a single class the annotation is
// silently ignored, and in a hierarchy the vtable slot is built read-only with the user's
// postcondition collapsed to `TheBalance == TheBalance + 7` — which is False.
using PalLang;

[Invariant("fracBalance >= 0")]
public sealed class FracMutates
{
    private int fracBalance;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Bal => fracBalance;

    [Spec]
    public SpecInt TheBalance => Bal;

    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public FracMutates(int b) { fracBalance = b; }

    [Frac("p")]
    [Requires("@this.TheBalance + 7 <= 2147483647")]
    [Ensures("@this.TheBalance == Old(@this.TheBalance) + 7")]
    public int Bonus() { fracBalance = fracBalance + 7; return fracBalance; }
}
