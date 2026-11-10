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

    // R32.10. A write through a node a call on the owned field found: the field's
    // invariant is folded again at the heap the write left, which keeps the tree's shape.
    [Ensures("Result == SpecSearchTree.Contains(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecNodes), item)")]
    [Ensures("@this.SpecNodes.Size == Pal.Old(@this.SpecNodes).Size")]
    [Ensures("Pal.Implies(!Result, @this.SpecNodes == Pal.Old(@this.SpecNodes))")]
    public bool Replace(U item, U replacement)
    {
        SearchTree<U>.Node? node = _tree.FindNode(item);
        if (node == null)
        {
            return false;
        }
        node.Item = replacement;
        return true;
    }

    // R32.2. `Contains` is `[Frac]` and calls the comparer through its interface: it is
    // read-only, so this method (and the borrowing class's below) is too.
    [Ensures("Result == SpecSearchTree.Contains(@this.SpecComparer, @this.SpecNodes, item)")]
    public bool Has(U item) => _tree.Contains(item);

    // R32.4. A tuple parameter rebound as a cell, and a field a call left open (R27.59) that
    // one arm of a tail `if` closes by calling on it, and the other closes at the return.
    [Ensures("Result == (flag && SpecSearchTree.Contains(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecNodes), pair.Item1))")]
    public bool ClearIfFound((U, bool) pair, bool flag)
    {
        pair = (pair.Item1, flag);
        SearchTree<U>.Node? node = _tree.FindNode(pair.Item1);
        if (node == null)
        {
            return false;
        }
        if (pair.Item2)
        {
            _tree.Clear();
            return true;
        }
        return false;
    }

    // R29.3, R32.1. A borrowing class whose constructor guards its non-nullable owner.
    public sealed class Items
    {
        private readonly TreeHolder<U> _holder;

        [Ensures("ReferenceEquals(@this._holder, holder)")]
        public Items(TreeHolder<U> holder)
        {
            System.ArgumentNullException.ThrowIfNull(holder);
            _holder = holder;
        }

        [Ensures("Result == SpecSearchTree.Contains(@this._holder.SpecComparer, @this._holder.SpecNodes, item)")]
        public bool Contains(U item) => _holder.Has(item);
    }
}
