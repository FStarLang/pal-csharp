// EXPECT: PALCS0561
// R10.5. The equation is inverted syntactically: the translator reads the invariant off
// *one* application of the model's non-empty constructor. An arbitrary expression over the
// sub-model is an equation with no induction to extract, and no rule says how to own the
// tail of a list that has had something appended to it.
using PalLang;

public sealed class AppendChain
{
    internal int value;
    internal AppendChain? next;

    [Model]
    private SpecList<SpecInt> Items =>
        SpecList.Append(next!.Elements, SpecList.Cons(value, SpecList.Empty<SpecInt>()));

    [Spec]
    public SpecList<SpecInt> Elements => Items;
}
