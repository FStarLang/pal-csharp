// EXPECT: PALCS0563
// R10.6. Every field of a recursive class other than the recursive one must be a value the
// cons case can state purely. An array contributes ownership of its own at every node, and
// the case lemmas would have to thread that ownership through the induction — a shape
// nothing has probed.
using PalLang;

public sealed class ChunkChain
{
    internal int[] data;
    internal ChunkChain? next;

    [Model]
    private SpecList<SpecInt> Items => SpecList.Cons(0, next!.Elements);

    [Spec]
    public SpecList<SpecInt> Elements => Items;
}
