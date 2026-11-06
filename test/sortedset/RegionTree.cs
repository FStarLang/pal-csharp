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

public sealed class SearchTree<T>
{
    private readonly IComparer<T> comparer;
    private Node? root;

    [Model]
    private TreeModel<T> Model => new TreeModel<T> { Nodes = Pal.Tree<(T, bool)>(root), Comparer = comparer };

    [Spec] public SpecTree<(T, bool)> SpecNodes => Model.Nodes;
    [Spec] public IComparer<T> SpecComparer => Model.Comparer;

    [Ensures("@this.SpecNodes.IsLeaf")]
    [Ensures("@this.SpecComparer == Comparer<T>.Default")]
    public SearchTree()
    {
        comparer = Comparer<T>.Default;
    }

    [Ensures("Result == SpecSearchTree.Contains(@this.SpecComparer, @this.SpecNodes, item)")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
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
            int order = comparer.Compare(item, current.Item);
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
