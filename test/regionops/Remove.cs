// Adapted from the annotated dotnet/runtime SortedSet in samples/dotnet-runtime.
// Licensed to the .NET Foundation under the MIT license.
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using PalLang;

public sealed partial class RbTree<T>
{
    [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) >= 0)")]
    [Ensures("@this.SpecItems == SpecTopDownRemove.Removed(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item)")]
    [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
    public bool Remove(T item)
    {
        if (root == null)
            return false;
        version++;
        Node? current = root;
        Node? parent = null;
        Node? grandParent = null;
        Node? match = null;
        Node? parentOfMatch = null;
        bool foundMatch = false;
#if PAL
        Ghost<Seq<T>> k0 = SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root));
        SpecTopDownRemove.Start<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root);
#endif
        while (current != null)
        {
#if PAL
            Pal.Decreases(SpecTopDownRemove.Measure<Node, T>(Pal.Heap<Node>(), root, current));
            Pal.Invariant(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) && version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
            Pal.Invariant(SpecTopDownRemove.RInv<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch));
            SpecTopDownRemove.AtCur<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch);
            Ghost<SpecHeap<Node>> h = Pal.Heap<Node>();
            Ghost<SpecInt> m0 = SpecTopDownRemove.Measure<Node, T>(h.Value, root, current);
#endif
            if (current.Is2Node)
            {
                if (parent == null)
                {
                    current.ColorRed();
#if PAL
                    SpecTopDownRemove.FixRoot<Node, T>(comparer, k0.Value, item, h.Value, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value);
#endif
                }
                else
                {
#if PAL
                    SpecTopDownRemove.SibPre<Node, T>(comparer, k0.Value, item, h.Value, root, current, parent, grandParent, match, parentOfMatch, foundMatch);
#endif
                    Node sibling = parent.GetSibling(current);
#if PAL
                    SpecTopDownRemove.AtSib<Node, T>(comparer, k0.Value, item, h.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch, m0.Value);
#endif
                    if (sibling.IsRed)
                    {
                        if (parent.Right == sibling)
                            parent.RotateLeft();
                        else
                            parent.RotateRight();
#if PAL
                        Ghost<SpecHeap<Node>> ha1 = Pal.Heap<Node>();
                        SpecTopDownRemove.AMid<Node, T>(comparer, k0.Value, item, h.Value, ha1.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch);
#endif
                        parent.ColorRed();
#if PAL
                        Ghost<SpecHeap<Node>> ha2 = Pal.Heap<Node>();
                        SpecTopDownRemove.ARed<Node, T>(comparer, k0.Value, item, h.Value, ha1.Value, ha2.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch);
#endif
                        sibling.ColorBlack();
#if PAL
                        Ghost<SpecHeap<Node>> ha3 = Pal.Heap<Node>();
                        Ghost<Node?> roota = root;
#endif
                        ReplaceChildOrRoot(grandParent, parent, sibling);
#if PAL
                        SpecTopDownRemove.AEnd<Node, T>(comparer, k0.Value, item, h.Value, ha1.Value, ha2.Value, ha3.Value, Pal.Heap<Node>(), roota.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch);
#endif
                        grandParent = sibling;
                        if (parent == match)
                            parentOfMatch = sibling;
#if PAL
                        SpecTopDownRemove.MidPre<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value);
#endif
                        sibling = parent.GetSibling(current);
                    }
#if PAL
                    Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) && version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
                    Pal.Join(SpecTopDownRemove.RMid<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value));
                    Pal.Join(current != null && parent != null && sibling != null);
                    Pal.Join(Pal.Implies(current == Pal.LeftOf(parent), sibling == Pal.RightOf(parent)) && Pal.Implies(current != Pal.LeftOf(parent), sibling == Pal.LeftOf(parent)));
                    SpecTopDownRemove.AtMid<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch, m0.Value);
#endif
                    Debug.Assert(current != null && parent != null && sibling != null);
#if PAL
                    Ghost<SpecHeap<Node>> hb = Pal.Heap<Node>();
#endif
                    if (sibling.Is2Node)
                    {
                        parent.Merge2Nodes();
#if PAL
                        SpecTopDownRemove.Merge<Node, T>(comparer, k0.Value, item, hb.Value, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch, m0.Value);
#endif
                    }
                    else
                    {
                        Node newGrandParent = parent.Rotate(parent.GetRotation(current, sibling))!;
#if PAL
                        Ghost<SpecHeap<Node>> hb1 = Pal.Heap<Node>();
                        SpecTopDownRemove.BRot<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
#endif
                        newGrandParent.Color = parent.Color;
#if PAL
                        Ghost<SpecHeap<Node>> hb2 = Pal.Heap<Node>();
                        SpecTopDownRemove.BColW<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, hb2.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
#endif
                        parent.ColorBlack();
#if PAL
                        Ghost<SpecHeap<Node>> hb3 = Pal.Heap<Node>();
                        SpecTopDownRemove.BBlk<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, hb2.Value, hb3.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
#endif
                        current.ColorRed();
#if PAL
                        Ghost<SpecHeap<Node>> hb4 = Pal.Heap<Node>();
                        SpecTopDownRemove.BCur<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, hb2.Value, hb3.Value, hb4.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
                        Ghost<Node?> rootb = root;
#endif
                        ReplaceChildOrRoot(grandParent, parent, newGrandParent);
#if PAL
                        SpecTopDownRemove.BEnd<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, hb2.Value, hb3.Value, hb4.Value, Pal.Heap<Node>(), rootb.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
#endif
                        if (parent == match)
                            parentOfMatch = newGrandParent;
                    }
                }
            }
#if PAL
            Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) && version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
            Pal.Join(current != null);
            Pal.Join(SpecTopDownRemove.RFx<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, match, parentOfMatch, foundMatch, m0.Value));
            SpecTopDownRemove.AtFx<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, match, parentOfMatch, foundMatch, m0.Value);
#endif
            Debug.Assert(current != null);
            int order = foundMatch ? -1 : comparer.Compare(item, current.Item);
#if PAL
            SpecTopDownRemove.Step<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, match, parentOfMatch, foundMatch, m0.Value, order, order == 0, order < 0);
#endif
            if (order == 0)
            {
                foundMatch = true;
                match = current;
                parentOfMatch = parent;
            }
            grandParent = parent;
            parent = current;
            current = order < 0 ? current.Left : current.Right;
        }
#if PAL
        SpecTopDownRemove.After<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, parent, grandParent, match, parentOfMatch, foundMatch);
        Ghost<Seq<T>> k1 = SpecTopDownRemove.Removed(comparer, k0.Value, item);
#endif
        if (match != null)
        {
#if PAL
            Ghost<SpecHeap<Node>> hr = Pal.Heap<Node>();
            Ghost<Node?> rootr = root;
#endif
            ReplaceNode(match, parentOfMatch!, parent!, grandParent!);
#if PAL
            SpecTopDownRemove.Replaced<Node, T>(comparer, k0.Value, item, hr.Value, Pal.Heap<Node>(), rootr.Value, root, match, parentOfMatch, parent, grandParent);
#endif
            --count;
        }
#if PAL
        Ghost<SpecHeap<Node>> hf = Pal.Heap<Node>();
#endif
        root?.ColorBlack();
#if PAL
        SpecTopDownRemove.Finish<Node, T>(comparer, k1.Value, hf.Value, Pal.Heap<Node>(), root);
#endif
        return foundMatch;
    }

    [Open]
    [Requires("SpecTopDownRemove.RnPre<RbTree<T>.Node, T>(Pal.Heap<RbTree<T>.Node>(), @this.root, match, parentOfMatch, successor, parentOfSuccessor)")]
    [Ensures("SpecTopDownRemove.RnPost<RbTree<T>.Node, T>(Pal.Old(Pal.Heap<RbTree<T>.Node>()), Pal.Heap<RbTree<T>.Node>(), Pal.Old(@this.root), @this.root, match)")]
    [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
    private void ReplaceNode(Node match, [AllowNull] Node parentOfMatch, Node successor, [AllowNull] Node parentOfSuccessor)
    {
#if PAL
        Ghost<SpecHeap<Node>> h0 = Pal.Heap<Node>();
        Ghost<Node?> root0 = root;
        Ghost<Node> succ0 = successor;
        SpecTopDownRemove.RnStart<Node, T>(h0.Value, root, match, parentOfMatch, successor, parentOfSuccessor);
#endif
        if (successor == match)
        {
#if PAL
            SpecTopDownRemove.RnA<Node, T>(h0.Value, root, match, parentOfMatch, successor, parentOfSuccessor);
#endif
            successor = match.Left!;
        }
        else
        {
            Debug.Assert(parentOfSuccessor != null);
            successor.Right?.ColorBlack();
#if PAL
            Ghost<SpecHeap<Node>> h1 = Pal.Heap<Node>();
#endif
            if (parentOfSuccessor != match)
            {
                parentOfSuccessor.Left = successor.Right;
                successor.Right = match.Right;
            }
            successor.Left = match.Left;
#if PAL
            SpecTopDownRemove.RnB<Node, T>(h0.Value, h1.Value, Pal.Heap<Node>(), root0.Value, match, parentOfMatch, successor, parentOfSuccessor);
#endif
        }
#if PAL
        Ghost<SpecHeap<Node>> h4 = Pal.Heap<Node>();
#endif
        if (successor != null)
            successor.Color = match.Color;
#if PAL
        Ghost<SpecHeap<Node>> h5 = Pal.Heap<Node>();
#endif
        ReplaceChildOrRoot(parentOfMatch, match, successor!);
#if PAL
        SpecTopDownRemove.RnDone<Node, T>(h0.Value, h4.Value, h5.Value, Pal.Heap<Node>(), root0.Value, root, match, parentOfMatch, succ0.Value, parentOfSuccessor, successor);
#endif
    }
}
