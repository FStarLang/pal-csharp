// EXPECT: PALCS0562
// R10.5. The recursion of the invariant is the recursion of the model, so a recursive field
// the model never reaches is memory the invariant has no way to own. C# would let the field
// be read; the translation would have nothing to read it out of.
using PalLang;

public sealed class ForgottenTail
{
    internal int value;
    internal ForgottenTail? next;

    [Model]
    private SpecList<SpecInt> Items => SpecList.Cons(value, SpecList.Empty<SpecInt>());

    [Spec]
    public SpecList<SpecInt> Elements => Items;
}
