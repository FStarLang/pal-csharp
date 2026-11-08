// R27. A binary search tree whose nodes are a `[Region]`: the owner holds every node as one
// region, `Pal.Tree` reads the tree a pointer reaches, and the searches are specified by the
// path they follow (`SpecSearchTree`), as dotnet/runtime's `SortedSet<T>` is.
using System.Collections.Generic;
using PalLang;

[Spec]
public struct TreeModel<T>
{
    public SpecTree<(T, bool)> Nodes;
    public IComparer<T> Comparer;
}

// R32.10. The owner's model also names its root pointer, so that a contract can say a
// node a search returns is one of the tree's nodes.
[Spec]
public struct SearchTreeModel<T>
{
    public SpecTree<(T, bool)> Nodes;
    public IComparer<T> Comparer;
    internal SearchTree<T>.Node? Root;
}

public sealed class SearchTree<T>
{
    private readonly IComparer<T> comparer;
    private Node? root;

    [Model]
    private SearchTreeModel<T> Model => new SearchTreeModel<T> { Nodes = Pal.Tree<(T, bool)>(root), Comparer = comparer, Root = root };

    [Spec] public SpecTree<(T, bool)> SpecNodes => Model.Nodes;
    [Spec] public IComparer<T> SpecComparer => Model.Comparer;
    [Spec] internal Node? SpecRoot => Model.Root;

    [Ensures("@this.SpecNodes.IsLeaf")]
    [Ensures("@this.SpecComparer == Comparer<T>.Default")]
    public SearchTree()
    {
        comparer = Comparer<T>.Default;
    }

    [Ensures("Result == SpecSearchTree.Contains(@this.SpecComparer, @this.SpecNodes, item)")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Frac("p")]
    public bool Contains(T item)
    {
        Node? current = root;
        while (current != null)
        {
            Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
            Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.WellFormed(current) &&
                          SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(current), item) ==
                          SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(root), item)));
            Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.ReturnValue<bool>() &&
                          SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(root), item)));
            int order = comparer.Compare(item, current!.Item);
            if (order == 0)
            {
                return true;
            }
            current = order < 0 ? current.Left : current.Right;
        }
        return false;
    }

    [Ensures("Pal.Implies(!@this.SpecNodes.IsLeaf, Pal.Same(Result, SpecSearchTree.Leftmost(@this.SpecNodes, Result)))")]
    public T? Min()
    {
        if (root == null)
        {
            return default;
        }
        Node current = root;
        while (current.Left != null)
        {
            Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
            Pal.Invariant(Pal.WellFormed(current) && !Pal.Same<Node?>(current, null));
            Pal.Invariant(Pal.Forall((T d) => Pal.Same(SpecSearchTree.Leftmost(Pal.Tree<(T, bool)>(current), d),
                                                       SpecSearchTree.Leftmost(Pal.Tree<(T, bool)>(root), d))));
            current = current.Left;
        }
        return current.Item;
    }

    // R27.13. The contract names the node the search returns at the owner's heap.
    [Ensures("(Result != null) == SpecSearchTree.Contains(@this.SpecComparer, @this.SpecNodes, item)")]
    [Ensures("Result == null || Pal.WellFormed(Result) && Pal.Same(SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Result), item), SpecSearchTree.Find(@this.SpecComparer, @this.SpecNodes, item, item))")]
    [Ensures("Result == null || SpecRegionWrite.InTree<SearchTree<T>.Node, T>(Pal.Heap<SearchTree<T>.Node>(), @this.SpecRoot, Result)")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
    internal Node? FindNode(T item)
    {
        Node? current = root;
        while (current != null)
        {
            Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
            Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.WellFormed(current) &&
                          SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(current), item) ==
                          SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(root), item) &&
                          (current == null || SpecRegionWrite.InTree<Node, T>(Pal.Heap<Node>(), root, current)) &&
                          Pal.Same(SpecSearchTree.Find(comparer, Pal.Tree<(T, bool)>(current), item, item),
                                   SpecSearchTree.Find(comparer, Pal.Tree<(T, bool)>(root), item, item))));
            Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.ReturnValue<Node?>() != null &&
                          SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(root), item) &&
                          Pal.WellFormed(Pal.ReturnValue<Node?>()) &&
                          SpecRegionWrite.InTree<Node, T>(Pal.Heap<Node>(), root, Pal.ReturnValue<Node?>()) &&
                          Pal.Same(SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Pal.ReturnValue<Node?>()), item),
                                   SpecSearchTree.Find(comparer, Pal.Tree<(T, bool)>(root), item, item))));
            int order = comparer.Compare(item, current!.Item);
            if (order == 0)
            {
                return current;
            }
            current = order < 0 ? current.Left : current.Right;
        }
        return null;
    }

    // R27.13. The caller reads the returned node: the receiver is opened at the same heap.
    [Ensures("Result == SpecSearchTree.Contains(@this.SpecComparer, @this.SpecNodes, item)")]
    [Ensures("Pal.Implies(Result, Pal.Same(found, SpecSearchTree.Find(@this.SpecComparer, @this.SpecNodes, item, item)))")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    public bool TryGet(T item, out T? found)
    {
        Node? node = FindNode(item);
        if (node != null)
        {
            found = node.Item;
            return true;
        }
        found = default;
        return false;
    }

    // R27.15. A loop whose arms write different locals after a short-circuit read.
    [Ensures("Result == null || Pal.WellFormed(Result) && SpecSearchTree.InRange(@this.SpecComparer, lo, hi, true, upper, SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Result), lo))")]
    [Ensures("(Result != null) == SpecSearchTree.RangeHit(@this.SpecComparer, @this.SpecNodes, lo, hi, true, upper)")]
    internal Node? FindRange(T lo, T hi, bool upper)
    {
        Node? current = root;
        while (current != null)
        {
            Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
            Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.WellFormed(current) &&
                          SpecSearchTree.RangeHit(comparer, Pal.Tree<(T, bool)>(current), lo, hi, true, upper) ==
                          SpecSearchTree.RangeHit(comparer, Pal.Tree<(T, bool)>(root), lo, hi, true, upper)));
            Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.ReturnValue<Node?>() != null &&
                          SpecSearchTree.RangeHit(comparer, Pal.Tree<(T, bool)>(root), lo, hi, true, upper) &&
                          Pal.WellFormed(Pal.ReturnValue<Node?>()) &&
                          SpecSearchTree.InRange(comparer, lo, hi, true, upper,
                                                 SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Pal.ReturnValue<Node?>()), lo))));
            if (comparer.Compare(lo, current.Item) > 0)
            {
                current = current.Right;
            }
            else if (upper && comparer.Compare(hi, current.Item) < 0)
            {
                current = current.Left;
            }
            else
            {
                return current;
            }
        }
        return null;
    }

    [Ensures("@this.SpecNodes.IsLeaf")]
    [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
    public void Clear()
    {
        root = null;
    }

    [Region]
    internal sealed class Node
    {
        public T Item;
        public Node? Left;
        public Node? Right;
        public bool IsRed;

        public Node(T item, bool isRed)
        {
            Item = item;
            IsRed = isRed;
            Left = null;
            Right = null;
        }

        [Model]
        private (T, bool) View => (Item, IsRed);
    }
}
