// EXPECT: PALCS0754
// R30.36, R30.43. A null test of a local of a recursive class narrows the local's
// predicate in each arm (R10.7), which a join would have to undo; it cannot be joined.
// A null test of a field narrows nothing and can.
using PalLang;

public sealed class Link
{
    internal int value;
    internal Link? next;

    [Model]
    private SpecList<int> Items => SpecList.Cons(value, next!.Items);

    [Spec]
    public SpecList<int> Elements => Items;
}

public static class Links
{
    [Ensures("0 <= Result && Result <= 1")]
    public static int NonEmpty([Frac("p")] Link? n)
    {
        int k = 0;
        if (n != null)
        {
            k = 1;
        }
        Pal.Join(0 <= k && k <= 1);
        return k;
    }
}
