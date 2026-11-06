// EXPECT: PALCS0703
// R27.7. `Pal.Tree` is a function of the heap of a region, so its argument must point into
// one: of a `[Plain]` class there is no heap to read the tree from.
using PalLang;

[Plain]
public sealed class Cell
{
    internal int Key;
    internal Cell? Left;
    internal Cell? Right;
}

public sealed class Holder
{
    internal Cell? cell;

    [Model]
    private SpecInt Model => 0;

    [Ensures("Pal.Tree<SpecInt>(@this.cell).Size >= 0")]
    public void Touch() { }
}
