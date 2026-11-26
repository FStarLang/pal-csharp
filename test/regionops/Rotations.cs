// Adapted from the annotated dotnet/runtime SortedSet in samples/dotnet-runtime.
// Licensed to the .NET Foundation under the MIT license.
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using PalLang;

[SpecType("Pulse.Lib.CSharp.SearchTree.tree_rotation")]
internal enum TreeRotation : byte
{
    [SpecCase("Pulse.Lib.CSharp.SearchTree.RotLeft")] Left,
    [SpecCase("Pulse.Lib.CSharp.SearchTree.RotLeftRight")] LeftRight,
    [SpecCase("Pulse.Lib.CSharp.SearchTree.RotRight")] Right,
    [SpecCase("Pulse.Lib.CSharp.SearchTree.RotRightLeft")] RightLeft
}

public sealed partial class RbTree<T>
{
    internal sealed partial class Node
    {
        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateRight(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Rotated<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this, Result, false, false)")]
        [Ensures("Result == Pal.Old(Pal.LeftOf(@this))")]
        public Node RotateRight()
        {
            Node child = Left!;
            Left = child.Right;
            child.Right = this;
            return child;
        }

        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !Pal.Tree<(T, bool)>(@this).Left.Right.IsLeaf")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateLeftRight(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Rotated<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this, Result, true, false)")]
        [Rlimit(10)]
        public Node RotateLeftRight()
        {
            Node child = Left!;
            Node grandChild = child.Right!;
            Left = grandChild.Right;
            grandChild.Right = this;
            child.Right = grandChild.Left;
            grandChild.Left = child;
            return grandChild;
        }

        [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf && !Pal.Tree<(T, bool)>(@this).Right.Left.IsLeaf")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateRightLeft(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDown.Rotated<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this, Result, false, true)")]
        [Rlimit(10)]
        [Fuel(0, 0)]
        public Node RotateRightLeft()
        {
            Node child = Right!;
            Node grandChild = child.Left!;
            Right = grandChild.Left;
            grandChild.Left = this;
            child.Left = grandChild.Right;
            grandChild.Right = child;
            return grandChild;
        }

        [Requires("Pal.Unshared(@this) && Pal.InRegion(sibling)")]
        [Requires("current == Pal.LeftOf(@this) && sibling == Pal.RightOf(@this) || current == Pal.RightOf(@this) && sibling == Pal.LeftOf(@this)")]
        [Requires("SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(sibling).Left) || SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(sibling).Right)")]
        [Ensures("Pal.Implies(current == Pal.LeftOf(@this), Result == (SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(sibling).Left) ? TreeRotation.RightLeft : TreeRotation.Left))")]
        [Ensures("Pal.Implies(current != Pal.LeftOf(@this), Result == (SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(sibling).Left) ? TreeRotation.Right : TreeRotation.LeftRight))")]
        [Ensures("SpecSearchTree.CanRotate(Result, Pal.Tree<(T, bool)>(@this))")]
        public TreeRotation GetRotation(Node current, Node sibling)
        {
            bool currentIsLeftChild = Left == current;
            return IsNonNullRed(sibling.Left) ?
                (currentIsLeftChild ? TreeRotation.RightLeft : TreeRotation.Right) :
                (currentIsLeftChild ? TreeRotation.Left : TreeRotation.LeftRight);
        }

        [Requires("Pal.Unshared(@this)")]
        [Requires("node == Pal.LeftOf(@this) && Pal.RightOf(@this) != null || node == Pal.RightOf(@this) && Pal.LeftOf(@this) != null")]
        [Requires("Pal.LeftOf(@this) != Pal.RightOf(@this)")]
        [Ensures("Pal.Implies(node == Pal.LeftOf(@this), Result == Pal.RightOf(@this))")]
        [Ensures("Pal.Implies(node != Pal.LeftOf(@this), Result == Pal.LeftOf(@this))")]
        public Node GetSibling(Node node) => node == Left ? Right! : Left!;

        [Requires("Pal.Unshared(@this) && SpecSearchTree.CanRotate(rotation, Pal.Tree<(T, bool)>(@this))")]
        [Ensures("Result != null && Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.Rotate(rotation, Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDownRemove.RotatedN<RbTree<T>.Node, T, TreeRotation>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this, Result, rotation)")]
        public Node? Rotate(TreeRotation rotation)
        {
#if PAL
            Ghost<SpecHeap<Node>> h0 = Pal.Heap<Node>();
#endif
            Node removeRed;
            switch (rotation)
            {
                case TreeRotation.Right:
                    removeRed = Left!.Left!;
                    removeRed.ColorBlack();
#if PAL
                    SpecTopDownRemove.RotSingle<Node, T>(h0.Value, Pal.Heap<Node>(), this, removeRed, false);
#endif
                    return RotateRight();
                case TreeRotation.Left:
                    removeRed = Right!.Right!;
                    removeRed.ColorBlack();
#if PAL
                    SpecTopDownRemove.RotSingle<Node, T>(h0.Value, Pal.Heap<Node>(), this, removeRed, true);
#endif
                    return RotateLeft();
                case TreeRotation.RightLeft:
#if PAL
                    SpecTopDownRemove.RotDouble<Node, T>(h0.Value, this, false);
#endif
                    return RotateRightLeft();
                case TreeRotation.LeftRight:
#if PAL
                    SpecTopDownRemove.RotDouble<Node, T>(h0.Value, this, true);
#endif
                    return RotateLeftRight();
                default:
                    Debug.Fail("Invalid rotation");
                    return null;
            }
        }

        [Requires("Pal.Unshared(@this) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this))")]
        [Requires("!Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left.Left) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left.Right)")]
        [Requires("!Pal.Tree<(T, bool)>(@this).Right.IsLeaf && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right.Left) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right.Right)")]
        [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
        [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Merge2(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
        [Ensures("SpecTopDownRemove.Merged<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this)")]
        public void Merge2Nodes()
        {
            Debug.Assert(Left != null && Right != null);
            ColorBlack();
            Left.ColorRed();
            Right.ColorRed();
        }

        [Requires("Pal.InRegion(@this)")]
        [Ensures("SpecTopDown.Relinked<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), @this, child, newChild)")]
        public void ReplaceChild(Node child, [AllowNull] Node newChild)
        {
            if (Left == child)
                Left = newChild;
            else
                Right = newChild;
        }
    }
}
