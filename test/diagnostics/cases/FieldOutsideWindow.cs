// EXPECT: PALCS0567
// R10.8. A recursive class's fields *are* reachable from outside the class — the client's
// own null test opens R10.7's window and `elim_cons` hands back the head cell. What is not
// reachable is a field of a reference nothing has tested, because the invariant is still
// folded around it and there is no non-null reference to project.
using PalLang;

public sealed class Cons2
{
    internal int value;
    internal Cons2? next;

    [Model]
    private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Items);

    [Spec]
    public SpecList<SpecInt> Elements => Items;
}

public static class Peek
{
    [Requires("c.Elements.Length > 0")]
    public static int Head(Cons2? c)
    {
        return c!.value;
    }
}
