// R27.58, R27.59. An object that owns a region owner through a field, as dotnet/runtime's
// `SortedDictionary` owns its `TreeSet`: a call on the field whose contract holds the field
// at its heaps converts it around the call, and a region pointer the call returns is read
// with the field kept open at the heap the call left it at.
using PalLang;

public sealed class TreeHolder<U>
{
    private readonly SearchTree<U> _tree;

    [Model]
    private TreeModel<U> Model => new TreeModel<U> { Nodes = _tree.SpecNodes, Comparer = _tree.SpecComparer };

    [Spec] public SpecTree<(U, bool)> SpecNodes => Model.Nodes;
    [Spec] public System.Collections.Generic.IComparer<U> SpecComparer => Model.Comparer;

    [Ensures("@this.SpecNodes.IsLeaf")]
    public TreeHolder()
    {
        _tree = new SearchTree<U>();
    }

    [Ensures("Result == SpecSearchTree.Contains(@this.SpecComparer, @this.SpecNodes, item)")]
    [Ensures("Pal.Implies(Result, Pal.Same(found, SpecSearchTree.Find(@this.SpecComparer, @this.SpecNodes, item, item)))")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    public bool Lookup(U item, out U? found)
    {
        SearchTree<U>.Node? node = _tree.FindNode(item);
        if (node == null)
        {
            found = default;
            return false;
        }
        found = node.Item;
        return true;
    }
}
