// Adapted from the annotated dotnet/runtime SortedSet in samples/dotnet-runtime.
// Licensed to the .NET Foundation under the MIT license.
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using PalLang;

public sealed partial class RbTree<T>
{
    [Requires("@this.SpecItems.Length < int.MaxValue")]
    [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) < 0)")]
    [Ensures("Pal.Implies(Result, @this.SpecItems == SpecTopDown.Inserted(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item))")]
    [Ensures("Pal.Implies(!Result, @this.SpecItems == Pal.Old(@this.SpecItems))")]
    [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
    public bool Add(T item)
    {
        if (root == null)
        {
            root = new Node(item, NodeColor.Black);
            count = 1;
            version++;
            return true;
        }

        Node? current = root;
        Node? parent = null;
        Node? grandParent = null;
        Node? greatGrandParent = null;
        version++;
#if PAL
        Ghost<Seq<T>> k0 = SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root));
        SpecTopDown.Start<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root);
#endif
        int order = 0;
        while (current != null)
        {
#if PAL
            Pal.Decreases(SpecTopDown.Measure<Node, T>(comparer, item, Pal.Heap<Node>(), root, current));
            Pal.Invariant(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount));
            Pal.Invariant(Pal.Implies(!Pal.Returned(),
                SpecTopDown.Inv<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, greatGrandParent, order)));
            Pal.Invariant(Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() &&
                Pal.KeyIndex(comparer, k0.Value, item) >= 0 && Pal.Unshared(root) &&
                SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)) == k0.Value &&
                SpecSearchTree.IsRedBlack(Pal.Tree<(T, bool)>(root)) &&
                Pal.Tree<(T, bool)>(root).Size == k0.Value.Length));
            SpecTopDown.AtCur<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, greatGrandParent, order);
            Ghost<SpecHeap<Node>> h = Pal.Heap<Node>();
            Ghost<SpecInt> m0 = SpecTopDown.Measure<Node, T>(comparer, item, h.Value, root, current);
            Ghost<int> order0 = order;
#endif
            order = comparer.Compare(item, current.Item);
#if PAL
            SpecTopDown.Look<Node, T>(comparer, k0.Value, item, h.Value, root, current, parent, grandParent, greatGrandParent, order0.Value, order);
#endif
            if (order == 0)
            {
                root.ColorBlack();
#if PAL
                SpecTopDown.Finish<Node, T>(comparer, k0.Value, h.Value, Pal.Heap<Node>(), root);
#endif
                return false;
            }
            if (current.Is4Node)
            {
                current.Split4Node();
#if PAL
                SpecTopDown.Split<Node, T>(comparer, k0.Value, item, h.Value, Pal.Heap<Node>(), root, current, parent, grandParent, greatGrandParent, order0.Value, order);
#endif
                if (Node.IsNonNullRed(parent))
                {
#if PAL
                    Ghost<SpecHeap<Node>> h1 = Pal.Heap<Node>();
                    Ghost<Node?> root1 = root;
                    Ghost<Node?> par1 = parent;
#endif
                    InsertionBalance(current, ref parent!, grandParent!, greatGrandParent!);
#if PAL
                    SpecTopDown.AfterBalance<Node, T>(comparer, k0.Value, item, h1.Value, Pal.Heap<Node>(), root1.Value, root, current, par1.Value, parent, grandParent, greatGrandParent, order, m0.Value);
#endif
                }
            }
            greatGrandParent = grandParent;
            grandParent = parent;
            parent = current;
            current = order < 0 ? current.Left : current.Right;
        }

#if PAL
        SpecTopDown.AtEnd<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, parent, grandParent, greatGrandParent, order);
        Ghost<SpecHeap<Node>> hl = Pal.Heap<Node>();
        Ghost<Seq<T>> k1 = SpecTopDown.Inserted(comparer, k0.Value, item);
#endif
        Debug.Assert(parent != null);
        Node node = new Node(item, NodeColor.Red);
        if (order > 0)
            parent.Right = node;
        else
            parent.Left = node;
#if PAL
        SpecTopDown.LinkedLeaf<Node, T>(comparer, k0.Value, item, hl.Value, Pal.Heap<Node>(), root, node, parent, grandParent, greatGrandParent, order);
#endif
        if (parent.IsRed)
        {
#if PAL
            Ghost<SpecHeap<Node>> h2 = Pal.Heap<Node>();
            Ghost<Node?> root2 = root;
            Ghost<Node?> par2 = parent;
#endif
            InsertionBalance(node, ref parent!, grandParent!, greatGrandParent!);
#if PAL
            SpecTopDown.AfterInsertBalance<Node, T>(comparer, k1.Value, h2.Value, Pal.Heap<Node>(), root2.Value, root, node, par2.Value, parent, greatGrandParent);
#endif
        }
#if PAL
        Ghost<SpecHeap<Node>> h3 = Pal.Heap<Node>();
#endif
        root.ColorBlack();
#if PAL
        SpecTopDown.FinishOk<Node, T>(comparer, k1.Value, h3.Value, Pal.Heap<Node>(), root);
#endif
        ++count;
        return true;
    }

    [Open]
    [Requires("parent != null")]
    [Requires("SpecTopDown.BalancePre<RbTree<T>.Node, T>(Pal.Heap<RbTree<T>.Node>(), @this.root, current, parent, grandParent, greatGrandParent)")]
    [Ensures("SpecTopDown.Balanced<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), Pal.Old(@this.root), @this.root, current, Pal.Old(parent), parent, greatGrandParent)")]
    [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
    private void InsertionBalance(Node current, ref Node parent, Node grandParent, [AllowNull] Node greatGrandParent)
    {
#if PAL
        Ghost<SpecHeap<Node>> h0 = Pal.Heap<Node>();
        Ghost<Node?> root0 = root;
        Ghost<Node> parent0 = parent;
        SpecTopDown.BalStart<Node, T>(h0.Value, root, current, parent, grandParent, greatGrandParent);
        SpecTopDown.BalGgp<Node, T>(h0.Value, root, current, parent, grandParent, greatGrandParent);
#endif
        bool parentIsOnRight = grandParent.Right == parent;
        bool currentIsOnRight = parent.Right == current;
#if PAL
        SpecTopDown.BalRot<Node, T>(h0.Value, root, current, parent, grandParent, greatGrandParent, currentIsOnRight, parentIsOnRight);
#endif
        Node newChildOfGreatGrandParent;
        if (parentIsOnRight == currentIsOnRight)
        {
            newChildOfGreatGrandParent = currentIsOnRight ? grandParent.RotateLeft() : grandParent.RotateRight();
        }
        else
        {
            newChildOfGreatGrandParent = currentIsOnRight ? grandParent.RotateLeftRight() : grandParent.RotateRightLeft();
            parent = greatGrandParent!;
        }
#if PAL
        Ghost<SpecHeap<Node>> h1 = Pal.Heap<Node>();
        SpecTopDown.BalMid<Node, T>(h0.Value, h1.Value, root0.Value, current, parent0.Value, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);
#endif
        grandParent.ColorRed();
#if PAL
        Ghost<SpecHeap<Node>> h2 = Pal.Heap<Node>();
        SpecTopDown.BalRed<Node, T>(h0.Value, h1.Value, h2.Value, root0.Value, current, parent0.Value, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);
#endif
        newChildOfGreatGrandParent.ColorBlack();
#if PAL
        Ghost<SpecHeap<Node>> h3 = Pal.Heap<Node>();
#endif
        ReplaceChildOrRoot(greatGrandParent, grandParent, newChildOfGreatGrandParent);
#if PAL
        SpecTopDown.BalEnd<Node, T>(h0.Value, h1.Value, h2.Value, h3.Value, Pal.Heap<Node>(), root0.Value, root, current, parent0.Value, parent, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);
#endif
    }

    [Open]
    [Requires("parent == null || Pal.InRegion(parent)")]
    [Ensures("SpecTopDown.Replaced<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), Pal.Old(@this.root), @this.root, parent, child, newChild)")]
    [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
    private void ReplaceChildOrRoot(Node? parent, Node child, [AllowNull] Node newChild)
    {
        if (parent != null)
            parent.ReplaceChild(child, newChild);
        else
            root = newChild;
    }
}
