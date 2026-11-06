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
}

[SpecType("Pulse.Lib.CSharp.SearchTree.node_color")]
public enum NodeColor : byte { Black, Red }

public sealed class RbTree<T>
{
    private Node? root;

    [Model]
    private RbModel<T> Model => new RbModel<T> { Nodes = Pal.Tree<(T, bool)>(root) };

    [Spec] public SpecTree<(T, bool)> SpecNodes => Model.Nodes;

    [Ensures("Result == (!@this.SpecNodes.IsLeaf && SpecSearchTree.IsRed(@this.SpecNodes))")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    public bool RootIsRed()
    {
        Pal.Assert(Pal.Implies(root != null, Pal.InRegion(root)));
        return Node.IsNonNullRed(root);
    }

    public void Clear() => root = null;

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
        }
    }

    [Region]
    internal sealed class Node
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
        [Rlimit(40)]
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
        public void ColorRed() => Color = NodeColor.Red;

        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Split4(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
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
        public Node RotateLeft()
        {
            Node child = Right!;
            Right = child.Left;
            child.Left = this;
            return child;
        }
    }
}
