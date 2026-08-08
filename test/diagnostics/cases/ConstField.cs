// EXPECT: PALCS0591
// R18.1. A `const` field is not state: it has no storage, so it is not part of the
// representation R9.4 builds, and there is no rule that makes its value visible to a
// specification. Until §9 has one, it is refused rather than dropped.
using PalLang;

public sealed class Limits
{
    private int n;

    [Model]
    private SpecInt TheN => n;

    public const int Max = 10;

    public Limits(int k)
    {
        this.n = k;
    }
}
