// EXPECT: PALCS0596
// R18.1. R4.12 builds the representation in the constructor, which is the single point
// where the class invariant is established. A field initialiser assigns before that runs,
// and the scheme has no rule for an assignment with no statement to attach it to.
using PalLang;

public sealed class Seeded
{
    private int n = 5;

    [Model]
    private SpecInt TheN => n;

    public Seeded()
    {
    }
}
