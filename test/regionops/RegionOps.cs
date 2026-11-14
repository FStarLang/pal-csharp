// R27.16. Members of a `[Region]` class: functions of the object and the region its owner
// holds, read-only (a fraction, the heap unchanged) or mutating (a new heap).
using System.Collections.Generic;
using System.Diagnostics;
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Spec]
public struct RbModel<T>
{
    public SpecTree<(T, bool)> Nodes;
    public IComparer<T> Comparer;
    public SpecInt Count;
    public SpecInt Version;
}

[SpecType("Pulse.Lib.CSharp.SearchTree.node_color")]
public enum NodeColor : byte { Black, Red }

public sealed partial class RbTree<T>
{
    private Node? root;
    private readonly IComparer<T> comparer;
    private int count;
    [Wrapping] private int version;

    [Refine("Pal.StrictlySorted(Result.Comparer, SpecSearchTree.Keys(Result.Nodes))")]
    [Refine("SpecSearchTree.IsRedBlack(Result.Nodes)")]
    [Refine("Result.Count == Result.Nodes.Size")]
    [Refine("Result.Comparer != null")]
    [Model]
    private RbModel<T> Model => new RbModel<T>
    {
        Nodes = Pal.Tree<(T, bool)>(root), Comparer = comparer, Count = count, Version = version
    };

    [Spec] public SpecTree<(T, bool)> SpecNodes => Model.Nodes;
    [Spec] public IComparer<T> SpecComparer => Model.Comparer;
    [Spec] public SpecInt SpecCount => Model.Count;
    [Spec] public SpecInt SpecVersion => Model.Version;
    [Spec] public Seq<T> SpecItems => SpecSearchTree.Keys(Model.Nodes);

    [Ensures("@this.SpecItems.Length == 0 && @this.SpecComparer == Comparer<T>.Default")]
    public RbTree()
    {
        comparer = Comparer<T>.Default;
    }

    [Ensures("@this.SpecItems.Length == 0")]
    [Ensures("@this.SpecComparer == (comparer == null ? Comparer<T>.Default : comparer)")]
    public RbTree(IComparer<T>? comparer)
    {
        this.comparer = comparer ?? Comparer<T>.Default;
    }

    [Ensures("Result == @this.SpecCount")]
    public int Count => count;

    [Ensures("Result == SpecSearchTree.Contains(@this.SpecComparer, @this.SpecNodes, item)")]
    [Ensures("Result == (Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0)")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
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
            int order = comparer.Compare(item, current.Item);
            if (order == 0)
                return true;
            current = order < 0 ? current.Left : current.Right;
        }
        return false;
    }

    [Ensures("Result == (!@this.SpecNodes.IsLeaf && SpecSearchTree.IsRed(@this.SpecNodes))")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    public bool RootIsRed()
    {
        Pal.Assert(Pal.Implies(root != null, Pal.InRegion(root)));
        return Node.IsNonNullRed(root);
    }

    [Ensures("@this.SpecItems.Length == 0")]
    [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
    public void Clear()
    {
        root = null;
        count = 0;
        version++;
    }

    [Ensures("@this.SpecNodes.IsLeaf == Pal.Old(@this.SpecNodes.IsLeaf)")]
    public void BlackenRoot()
    {
        if (root != null)
        {
            root.ColorBlack();
        }
    }

    [Ensures("Pal.Old(@this.SpecNodes.IsLeaf) ? @this.SpecNodes == SpecTree.Branch(SpecTree.Leaf<(T, bool)>(), (item, false), SpecTree.Leaf<(T, bool)>()) : @this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    public void AddFirst(T item)
    {
        if (root == null)
        {
            root = new Node(item, NodeColor.Black);
            count = 1;
        }
    }

    [Region]
    internal sealed partial class Node
    {
        public Node(T item, NodeColor color)
        {
            Item = item;
            Color = color;
        }

        [Requires("node == null || Pal.InRegion(node)")]
        [Ensures("Result == (node != null && Pal.InRegion(node) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(node)))")]
        public static bool IsNonNullRed(Node? node) => node != null && node.IsRed;

        public T Item { get; set; }

        public Node? Left { get; set; }

        public Node? Right { get; set; }

        public NodeColor Color { get; set; }

        [Model]
        private (T, bool) View => (Item, Color == NodeColor.Red);

        [Requires("Pal.InRegion(@this)")]
        [Ensures("Result == SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this))")]
        public bool IsRed => Color == NodeColor.Red;

        [Requires("Pal.Unshared(@this)")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Recolor(Pal.Old(Pal.Tree<(T, bool)>(@this)), false)")]
        [Ensures("SpecTopDown.Recolored<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this, false)")]
        [Rlimit(10)]
        public void ColorBlack() => Color = NodeColor.Black;

        [Requires("node == null || Pal.InRegion(node)")]
        [Ensures("Result == (node != null && Pal.InRegion(node) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(node)))")]
        public static bool IsNonNullBlack(Node? node) => node != null && node.IsBlack;

        [Requires("node == null || Pal.InRegion(node)")]
        [Ensures("Result == (node == null || !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(node)))")]
        public static bool IsNullOrBlack(Node? node) => node == null || node.IsBlack;

        [Requires("Pal.InRegion(@this)")]
        [Ensures("Result == !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this))")]
        public bool IsBlack => Color == NodeColor.Black;

        [Requires("Pal.WellFormed(@this)")]
        [Ensures("Result == (!SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this)) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right))")]
        public bool Is2Node => IsBlack && IsNullOrBlack(Left) && IsNullOrBlack(Right);

        [Requires("Pal.WellFormed(@this)")]
        [Ensures("Result == (SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right))")]
        public bool Is4Node => IsNonNullRed(Left) && IsNonNullRed(Right);

        [Requires("Pal.Unshared(@this)")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Recolor(Pal.Old(Pal.Tree<(T, bool)>(@this)), true)")]
        [Ensures("SpecTopDown.Recolored<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this, true)")]
        public void ColorRed() => Color = NodeColor.Red;

        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Split4(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Split4ed<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this)")]
        public void Split4Node()
        {
            Debug.Assert(Left != null);
            Debug.Assert(Right != null);

            ColorRed();
            Left.ColorBlack();
            Right.ColorBlack();
        }

        [Requires("Pal.InRegion(@this)")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(null, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == Pal.Old(Pal.Tree<(T, bool)>(@this)).RootOnly")]
        public Node ShallowClone() => new Node(Item, Color);

        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateLeft(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Rotated<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this, Result, true, true)")]
        [Ensures("Result == Pal.Old(Pal.RightOf(@this))")]
        public Node RotateLeft()
        {
            Node child = Right!;
            Right = child.Left;
            child.Left = this;
            return child;
        }
    }
}
