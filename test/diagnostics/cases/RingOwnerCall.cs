// EXPECT: PALCS0781
// R31.11. A ring node's member that reads its owner through the back pointer is given the
// owner's box by the owner's own instance methods; a node method cannot supply it.
using PalLang;

[Invariant("SpecRing.Ring<Link, Chain>(Pal.Heap<Link>(), first, size, @this)")]
public sealed class Chain
{
    internal Link? first;
    internal int size;

    [Model] private SpecInt Model => size;
}

[Region(Cyclic = true)]
public sealed class Link
{
    internal Chain? owner;
    internal Link? next;
    internal Link? prev;
    internal int value;

    [Model] private (int, Chain?) View => (value, owner);

    [Requires("Pal.InRegion(@this)")]
    public Link? Next => next == null || next == owner!.first ? null : next;

    [Requires("Pal.InRegion(@this)")]
    public Link? Second() => Next;
}
