// EXPECT: PALCS0569
// R10.7. The null test is what opens the window in which a recursive class's fields are
// reachable, and a window's extent is a branch. Written inside a `&&` there is no branch
// for it to be the extent of: the reference would be tested in one place and used in
// another, with nothing carrying the case analysis between them.
using PalLang;

public sealed class Cell5
{
    internal int value;
    internal Cell5? next;

    [Model]
    private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Items);

    [Spec]
    public SpecList<SpecInt> Elements => Items;
}

public static class Walk5
{
    public static bool Pair(Cell5? a, Cell5? b)
    {
        return a != null && b != null;
    }
}
