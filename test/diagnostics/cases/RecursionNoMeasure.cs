// EXPECT: PALCS0568
// R10.7's counterpart to R5.9. A self-recursive method becomes `fn rec`, and F2 applies to
// it exactly as it applies to a loop: without a `decreases` the definition is divergent and
// no caller can compose with it. A loop has a counted-`for` case to fall back on; a
// recursion's measure is a term over the model, and guessing one would be inventing a proof
// step (§0 rule 3). So the two answers are the user's and a refusal.
using PalLang;

public sealed class Cell4
{
    internal int value;
    internal Cell4? next;

    [Model]
    private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Items);

    [Spec]
    public SpecList<SpecInt> Elements => Items;
}

public static class Walk4
{
    [Requires("n.Elements.Length < 2147483647")]
    [Ensures("Result == n.Elements.Length")]
    public static int Len(Cell4? n)
    {
        if (n == null)
        {
            return 0;
        }
        return 1 + Len(n.next);
    }
}
