// EXPECT: PALCS0705
// R27.16. `new` on a `[Region]` class is an allocation only when the constructor just
// assigns its parameters to fields.
using PalLang;

[Spec]
public struct Holder
{
    public SpecTree<int> Nodes;
}

public sealed class Owner
{
    private Node? root;

    [Model] private Holder Model => new Holder { Nodes = Pal.Tree<int>(root) };

    [Ensures("true")]
    public void Plant(int v)
    {
        root = new Node(v);
    }

    [Region]
    internal sealed class Node
    {
        public Node(int item)
        {
            Item = item + 1;
        }

        public int Item { get; set; }

        public Node? Left { get; set; }

        public Node? Right { get; set; }

        [Model] private int View => Item;
    }
}
