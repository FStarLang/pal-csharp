// R27.21-R27.28. The top-down red-black insertion of dotnet/runtime's `SortedSet<T>`,
// verified against the set it denotes: a `[Region]` of nodes rewritten in place, `[Open]`
// helpers whose contracts name the owner's fields and heap, a `ref` region pointer, and a
// loop whose measure reads the heap the loop writes (`Region.current`).
using System.Collections.Generic;
using System.Diagnostics;
using PalLang;

[SpecType("Pulse.Lib.CSharp.SearchTree.node_color")]
internal enum NodeColor : byte
{
    Black,
    Red
}

[Spec]
public struct RbModel<T>
{
    public SpecTree<(T, bool)> Tree;
    public IComparer<T> Comparer;
    public SpecInt Count;
}

public sealed class RbSet<T>
{
    private RbNode? root;
    private IComparer<T> comparer;
    private int count;
    [Wrapping] private int version;

    [Refine("Pal.StrictlySorted(Result.Comparer, SpecSearchTree.Keys(Result.Tree))")]
    [Refine("SpecSearchTree.IsRedBlack(Result.Tree)")]
    [Refine("Result.Count == Result.Tree.Size")]
    [Model]
    private RbModel<T> Model => new RbModel<T> { Tree = Pal.Tree<(T, bool)>(root), Comparer = comparer, Count = count };

    [Spec] public SpecInt SpecCount => Model.Count;
    [Spec] public IComparer<T> SpecComparer => Model.Comparer;
    [Spec] public Seq<T> SpecItems => SpecSearchTree.Keys(Model.Tree);

    [Ensures("@this.SpecItems.Length == 0")]
    public RbSet()
    {
        comparer = Comparer<T>.Default;
    }

    [Requires("@this.SpecItems.Length < int.MaxValue")]
    [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) < 0)")]
    [Ensures("Pal.Implies(Result, @this.SpecItems == SpecTopDown.Inserted(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item))")]
    [Ensures("Pal.Implies(!Result, @this.SpecItems == Pal.Old(@this.SpecItems))")]
    [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
    public bool Add(T item)
    {
        if (root == null)
        {
            // The tree is empty and this is the first item.
            root = new RbNode(item, NodeColor.Black);
            count = 1;
            version++;
            return true;
        }

        // Search for a node at bottom to insert the new node.
        // If we can guarantee the node we found is not a 4-node, it would be easy to do insertion.
        // We split 4-nodes along the search path.
        RbNode? current = root;
        RbNode? parent = null;
        RbNode? grandParent = null;
        RbNode? greatGrandParent = null;

        // Even if we don't actually add to the set, we may be altering its structure (by doing rotations and such).
        // So update `_version` to disable any instances of Enumerator/TreeSubSet from working on it.
        version++;

        Ghost<Seq<T>> k0 = SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root));
        SpecTopDown.Start<RbNode, T>(comparer, k0.Value, item, Pal.Heap<RbNode>(), root);

        int order = 0;
        while (current != null)
        {
            Pal.Decreases(SpecTopDown.Measure<RbNode, T>(comparer, item, Pal.Heap<RbNode>(), root, current));
            Pal.Invariant(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount));
            Pal.Invariant(Pal.Implies(!Pal.Returned(),
                SpecTopDown.Inv<RbNode, T>(comparer, k0.Value, item, Pal.Heap<RbNode>(), root, current, parent, grandParent, greatGrandParent, order)));
            Pal.Invariant(Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() &&
                Pal.KeyIndex(comparer, k0.Value, item) >= 0 && Pal.Unshared(root) &&
                SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)) == k0.Value &&
                SpecSearchTree.IsRedBlack(Pal.Tree<(T, bool)>(root)) &&
                Pal.Tree<(T, bool)>(root).Size == k0.Value.Length));
            SpecTopDown.AtCur<RbNode, T>(comparer, k0.Value, item, Pal.Heap<RbNode>(), root, current, parent, grandParent, greatGrandParent, order);
            Ghost<SpecHeap<RbNode>> h = Pal.Heap<RbNode>();
            Ghost<SpecInt> m0 = SpecTopDown.Measure<RbNode, T>(comparer, item, h.Value, root, current);
            Ghost<int> order0 = order;
            order = comparer.Compare(item, current.Item);
            SpecTopDown.Look<RbNode, T>(comparer, k0.Value, item, h.Value, root, current, parent, grandParent, greatGrandParent, order0.Value, order);
            if (order == 0)
            {
                // We could have changed root node to red during the search process.
                // We need to set it to black before we return.
                root.ColorBlack();
                SpecTopDown.Finish<RbNode, T>(comparer, k0.Value, h.Value, Pal.Heap<RbNode>(), root);
                return false;
            }

            // Split a 4-node into two 2-nodes.
            if (current.Is4Node)
            {
                current.Split4Node();
                SpecTopDown.Split<RbNode, T>(comparer, k0.Value, item, h.Value, Pal.Heap<RbNode>(), root, current, parent, grandParent, greatGrandParent, order0.Value, order);
                // We could have introduced two consecutive red nodes after split. Fix that by rotation.
                if (RbNode.IsNonNullRed(parent))
                {
                    Ghost<SpecHeap<RbNode>> h1 = Pal.Heap<RbNode>();
                    Ghost<RbNode?> root1 = root;
                    Ghost<RbNode?> par1 = parent;
                    InsertionBalance(current, ref parent!, grandParent!, greatGrandParent!);
                    SpecTopDown.AfterBalance<RbNode, T>(comparer, k0.Value, item, h1.Value, Pal.Heap<RbNode>(), root1.Value, root, current, par1.Value, parent, grandParent, greatGrandParent, order, m0.Value);
                }
            }

            greatGrandParent = grandParent;
            grandParent = parent;
            parent = current;
            current = (order < 0) ? current.Left : current.Right;
        }

        SpecTopDown.AtEnd<RbNode, T>(comparer, k0.Value, item, Pal.Heap<RbNode>(), root, parent, grandParent, greatGrandParent, order);
        Ghost<SpecHeap<RbNode>> hl = Pal.Heap<RbNode>();
        Ghost<Seq<T>> k1 = SpecTopDown.Inserted(comparer, k0.Value, item);
        Debug.Assert(parent != null);
        // We're ready to insert the new node.
        RbNode node = new RbNode(item, NodeColor.Red);
        if (order > 0)
        {
            parent.Right = node;
        }
        else
        {
            parent.Left = node;
        }
        SpecTopDown.LinkedLeaf<RbNode, T>(comparer, k0.Value, item, hl.Value, Pal.Heap<RbNode>(), root, node, parent, grandParent, greatGrandParent, order);

        // The new node will be red, so we will need to adjust colors if its parent is also red.
        if (parent.IsRed)
        {
            Ghost<SpecHeap<RbNode>> h2 = Pal.Heap<RbNode>();
            Ghost<RbNode?> root2 = root;
            Ghost<RbNode?> par2 = parent;
            InsertionBalance(node, ref parent!, grandParent!, greatGrandParent!);
            SpecTopDown.AfterInsertBalance<RbNode, T>(comparer, k1.Value, h2.Value, Pal.Heap<RbNode>(), root2.Value, root, node, par2.Value, parent, greatGrandParent);
        }

        // The root node is always black.
        Ghost<SpecHeap<RbNode>> h3 = Pal.Heap<RbNode>();
        root.ColorBlack();
        SpecTopDown.FinishOk<RbNode, T>(comparer, k1.Value, h3.Value, Pal.Heap<RbNode>(), root);
        ++count;
        return true;
    }

    [Open]
    [Requires("parent != null")]
    [Requires("SpecTopDown.BalancePre<RbSet<T>.RbNode, T>(Pal.Heap<RbSet<T>.RbNode>(), @this.root, current, parent, grandParent, greatGrandParent)")]
    [Ensures("SpecTopDown.Balanced<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), Pal.Old(@this.root), @this.root, current, Pal.Old(parent), parent, greatGrandParent)")]
    [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
    private void InsertionBalance(RbNode current, ref RbNode parent, RbNode grandParent, [System.Diagnostics.CodeAnalysis.AllowNull] RbNode greatGrandParent)
    {
        Debug.Assert(parent != null);
        Debug.Assert(grandParent != null);

        Ghost<SpecHeap<RbNode>> h0 = Pal.Heap<RbNode>();
        Ghost<RbNode?> root0 = root;
        Ghost<RbNode> parent0 = parent;
        SpecTopDown.BalStart<RbNode, T>(h0.Value, root, current, parent, grandParent, greatGrandParent);
        SpecTopDown.BalGgp<RbNode, T>(h0.Value, root, current, parent, grandParent, greatGrandParent);
        bool parentIsOnRight = grandParent.Right == parent;
        bool currentIsOnRight = parent.Right == current;
        SpecTopDown.BalRot<RbNode, T>(h0.Value, root, current, parent, grandParent, greatGrandParent, currentIsOnRight, parentIsOnRight);

        RbNode newChildOfGreatGrandParent;
        if (parentIsOnRight == currentIsOnRight)
        {
            // Same orientation, single rotation
            newChildOfGreatGrandParent = currentIsOnRight ? grandParent.RotateLeft() : grandParent.RotateRight();
        }
        else
        {
            // Different orientation, double rotation
            newChildOfGreatGrandParent = currentIsOnRight ? grandParent.RotateLeftRight() : grandParent.RotateRightLeft();
            // Current node now becomes the child of `greatGrandParent`
            parent = greatGrandParent!;
        }

        Ghost<SpecHeap<RbNode>> h1 = Pal.Heap<RbNode>();
        SpecTopDown.BalMid<RbNode, T>(h0.Value, h1.Value, root0.Value, current, parent0.Value, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);

        // `grandParent` will become a child of either `parent` of `current`.
        grandParent.ColorRed();
        Ghost<SpecHeap<RbNode>> h2 = Pal.Heap<RbNode>();
        SpecTopDown.BalRed<RbNode, T>(h0.Value, h1.Value, h2.Value, root0.Value, current, parent0.Value, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);
        newChildOfGreatGrandParent.ColorBlack();
        Ghost<SpecHeap<RbNode>> h3 = Pal.Heap<RbNode>();

        ReplaceChildOrRoot(greatGrandParent, grandParent, newChildOfGreatGrandParent);
        SpecTopDown.BalEnd<RbNode, T>(h0.Value, h1.Value, h2.Value, h3.Value, Pal.Heap<RbNode>(), root0.Value, root, current, parent0.Value, parent, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);
    }

    [Open]
    [Requires("parent == null || Pal.InRegion(parent)")]
    [Ensures("SpecTopDown.Replaced<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), Pal.Old(@this.root), @this.root, parent, child, newChild)")]
    [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
    private void ReplaceChildOrRoot(RbNode? parent, RbNode child, RbNode newChild)
    {
        if (parent != null)
        {
            parent.ReplaceChild(child, newChild);
        }
        else
        {
            root = newChild;
        }
    }

    // R27.29. A statement `x?.M()` on a region pointer, and a region parameter re-assigned.
    [Open]
    [Requires("x == null || Pal.Unshared(x)")]
    [Ensures("x == null || Pal.Tree<(T, bool)>(x) == SpecSearchTree.Recolor(Pal.Old(Pal.Tree<(T, bool)>(x)), false)")]
    [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
    private void BlackenIfAny(RbNode? x)
    {
        x?.ColorBlack();
    }

    [Open]
    [Requires("x == null || Pal.InRegion(x)")]
    [Requires("y == null || Pal.InRegion(y)")]
    [Ensures("Pal.Implies(x != null, Result == SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(x)))")]
    [Ensures("Pal.Implies(x == null, Result == (y != null && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(y))))")]
    private bool FirstIsRed(RbNode? x, RbNode? y)
    {
        if (x == null)
        {
            x = y;
        }
        return RbNode.IsNonNullRed(x);
    }

    // R27.31. The same loop in an `[Open]` method, which carries the owner's heap and reads
    // its fields from the record the loop holds.
    [Open]
    [Requires("Pal.Unshared(x)")]
    [Ensures("Pal.Unshared(x)")]
    [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
    private void RepaintOpen(RbNode x, int n, bool red)
    {
        int i = 0;
        while (i < n)
        {
            Pal.Decreases(n - i);
            Pal.Invariant(Pal.Unshared(x));
            Pal.Invariant(comparer == Pal.Old(this.comparer) && count == Pal.Old(this.count) && version == Pal.Old(this.version));
            if (red)
            {
                x.ColorRed();
            }
            else
            {
                x.ColorBlack();
            }
            i++;
        }
    }

    [Region]
    internal sealed class RbNode
    {
        public RbNode(T item, NodeColor color)
        {
            Item = item;
            Color = color;
        }

        [Requires("node == null || Pal.InRegion(node)")]
        [Ensures("Result == (node != null && Pal.InRegion(node) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(node)))")]
        public static bool IsNonNullRed(RbNode? node) => node != null && node.IsRed;

        public T Item { get; set; }

        public RbNode? Left { get; set; }

        public RbNode? Right { get; set; }

        public NodeColor Color { get; set; }

        [Model]
        private (T, bool) View => (Item, Color == NodeColor.Red);

        [Requires("Pal.InRegion(@this)")]
        [Ensures("Result == !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this))")]
        public bool IsBlack => Color == NodeColor.Black;

        [Requires("Pal.InRegion(@this)")]
        [Ensures("Result == SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this))")]
        public bool IsRed => Color == NodeColor.Red;

        [Requires("Pal.WellFormed(@this)")]
        [Ensures("Result == (SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right))")]
        public bool Is4Node => IsNonNullRed(Left) && IsNonNullRed(Right);

        // R27.31. A loop body whose `if` moves the region: each arm carries the rest of the
        // body, so what the arm proves about the heap it leaves reaches the invariant.
        [Requires("Pal.Unshared(@this)")]
        [Ensures("Pal.Unshared(@this)")]
        public void Repaint(int n, bool red)
        {
            int i = 0;
            while (i < n)
            {
                Pal.Decreases(n - i);
                Pal.Invariant(Pal.Unshared(this));
                if (red)
                {
                    ColorRed();
                }
                else
                {
                    ColorBlack();
                }
                i++;
            }
        }

        // R27.16: `Pal.Heap` in a ghost statement is the heap as it stands, not as it was on
        // entry. R27.31: a discarded non-`void` result.
        [Requires("Pal.Unshared(@this)")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        public void Blacken()
        {
            Ghost<SpecHeap<RbNode>> h0 = Pal.Heap<RbNode>();
            ColorBlack();
            Ghost<SpecHeap<RbNode>> h1 = Pal.Heap<RbNode>();
            Pal.Assert(SpecTopDown.Recolored<RbSet<T>.RbNode, T>(h0.Value, h1.Value, this, false));
            IsNonNullRed(null);
        }

        [Requires("Pal.Unshared(@this)")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Recolor(Pal.Old(Pal.Tree<(T, bool)>(@this)), false)")]
        [Ensures("SpecTopDown.Recolored<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), @this, false)")]
        public void ColorBlack() => Color = NodeColor.Black;

        [Requires("Pal.Unshared(@this)")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Recolor(Pal.Old(Pal.Tree<(T, bool)>(@this)), true)")]
        [Ensures("SpecTopDown.Recolored<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), @this, true)")]
        public void ColorRed() => Color = NodeColor.Red;

        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Split4(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Split4ed<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), @this)")]
        public void Split4Node()
        {
            Debug.Assert(Left != null);
            Debug.Assert(Right != null);

            ColorRed();
            Left.ColorBlack();
            Right.ColorBlack();
        }

        /// <summary>
        /// Does a left rotation on this tree, making this node the new left child of the current right child.
        /// </summary>
        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateLeft(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Rotated<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), @this, Result, true, true)")]
        public RbNode RotateLeft()
        {
            RbNode child = Right!;
            Right = child.Left;
            child.Left = this;
            return child;
        }

        /// <summary>
        /// Does a left-right rotation on this tree. The left child is rotated left, then this node is rotated right.
        /// </summary>
        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !Pal.Tree<(T, bool)>(@this).Left.Right.IsLeaf")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateLeftRight(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Rotated<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), @this, Result, true, false)")]
        [Rlimit(200)]
        public RbNode RotateLeftRight()
        {
            RbNode child = Left!;
            RbNode grandChild = child.Right!;

            Left = grandChild.Right;
            grandChild.Right = this;
            child.Right = grandChild.Left;
            grandChild.Left = child;
            return grandChild;
        }

        /// <summary>
        /// Does a right rotation on this tree, making this node the new right child of the current left child.
        /// </summary>
        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateRight(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Rotated<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), @this, Result, false, false)")]
        public RbNode RotateRight()
        {
            RbNode child = Left!;
            Left = child.Right;
            child.Right = this;
            return child;
        }

        /// <summary>
        /// Does a right-left rotation on this tree. The right child is rotated right, then this node is rotated left.
        /// </summary>
        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf && !Pal.Tree<(T, bool)>(@this).Right.Left.IsLeaf")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateRightLeft(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Rotated<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), @this, Result, false, true)")]
        [Rlimit(200)]
        public RbNode RotateRightLeft()
        {
            RbNode child = Right!;
            RbNode grandChild = child.Left!;

            Right = grandChild.Left;
            grandChild.Left = this;
            child.Left = grandChild.Right;
            grandChild.Right = child;
            return grandChild;
        }

        /// <summary>
        /// Replaces a child of this node with a new node.
        /// </summary>
        /// <param name="child">The child to replace.</param>
        /// <param name="newChild">The node to replace <paramref name="child"/> with.</param>
        [Requires("Pal.InRegion(@this)")]
        [Ensures("SpecTopDown.Relinked<RbSet<T>.RbNode, T>(Pal.Old(Pal.Heap<RbSet<T>.RbNode>()), Pal.Heap<RbSet<T>.RbNode>(), @this, child, newChild)")]
        public void ReplaceChild(RbNode child, RbNode newChild)
        {
            if (Left == child)
            {
                Left = newChild;
            }
            else
            {
                Right = newChild;
            }
        }
    }
}
