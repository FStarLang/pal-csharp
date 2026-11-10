// EXPECT: PALCS0780
// R31.1. A cyclic region has no tree: `Pal.Tree` over one is refused.
using PalLang;

[Spec]
public struct Holder
{
    public SpecTree<int> Nodes;
}

public sealed class Owner
{
    private Node? first;

    [Model] private Holder Model => new Holder { Nodes = Pal.Tree<int>(first) };

    [Region(Cyclic = true)]
    internal sealed class Node
    {
        internal Node? next;
        internal Node? prev;
        internal int item;

        [Model] private int View => item;
    }
}
