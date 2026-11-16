using System.Collections.Generic;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static partial class RbTree
{
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && root == RbCursorSpec.Top(nodes)")]
    [Requires("SpecSearchTree.IsRedBlack(RbCursorSpec.Strip(nodes))")]
    [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)))")]
    [Ensures("RbAddSpec.Labelled(Result, comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)), key)")]
    private static RbNode<T>? AddTopDown<T>(RbNode<T>? root, T key, IComparer<T> comparer,
        Ghost<RbLabels<T>> nodes = default)
    {
        RbNode<T>? result = root;
        bool changed = AddCore(ref result, key, comparer);
        return result;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && root == RbCursorSpec.Top(nodes)")]
    [Requires("SpecSearchTree.IsRedBlack(RbCursorSpec.Strip(nodes))")]
    [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)))")]
    [Ensures("RbAddSpec.Labelled(root, comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)), key)")]
    private static bool AddCore<T>(ref RbNode<T>? root, T key, IComparer<T> comparer,
        Ghost<RbLabels<T>> nodes = default)
    {
        if (root == null)
        {
            RbAddProof.ReleaseEmpty(nodes);
            RbNode<T> singleton = NewLeaf(key, false);
            RbAddProof.Singleton(singleton, comparer, key);
            root = singleton;
            return true;
        }
#if PAL
        Ghost<Seq<T>> keys = SpecSearchTree.Keys(RbCursorSpec.Strip(nodes.Value));
        RbState<T> state = RbState.Start(nodes);
#endif
        RbNode<T>? current = root;
        RbNode<T>? parent = root;
        RbNode<T>? grandParent = root;
        RbNode<T>? greatGrandParent = root;
        parent = null;
        grandParent = null;
        greatGrandParent = null;
        RbAddProof.Start(comparer, key, nodes);
        int order = 0;
        while (current != null)
        {
#if PAL
            Pal.Decreases(RbAddSpec.Measure(comparer, key, RbState.Labels(state), current));
            Pal.Invariant(RbCursorSpec.Owns(RbState.Labels(state)));
            Pal.Invariant(root == RbCursorSpec.Top(RbState.Labels(state)));
            Pal.Invariant(Pal.Implies(!Pal.Returned(), RbAddSpec.Inv(comparer, keys.Value, key,
                RbState.Labels(state), current, parent, grandParent, greatGrandParent, order)));
            Pal.Invariant(Pal.Implies(Pal.Returned(), RbAddSpec.Complete(comparer, keys.Value, key,
                root, RbState.Labels(state))));
            Ghost<RbLabels<T>> before = RbState.Labels(state);
            RbCursorProof.Change<T>(RbState.Labels(state), before);
            Ghost<int> oldOrder = order;
            Ghost<SpecInt> measure = RbAddSpec.Measure(comparer, key, before.Value, current);
            RbAddProof.AtCur(comparer, keys, key, before, current, parent, grandParent, greatGrandParent, order);
            RbCursorProof.Open(current, before);
#endif
            T value = current.key;
            order = comparer.Compare(key, value);
#if PAL
            RbCursorProof.Close(current, before);
            Pal.Assert(order == RbAddSpec.Comparison(comparer, key, before.Value, current));
            RbAddProof.Look(comparer, keys, key, before, current, parent, grandParent, greatGrandParent, oldOrder.Value, order);
#endif
            if (order == 0)
            {
#if PAL
                RbAddProof.Finish(comparer, keys, key, before);
#endif
                ColorLocal(root!, false);
#if PAL
                state = RbState.Black(state);
                RbCursorProof.Change<T>(RbSplitSpec.Color(before.Value, false), RbState.Labels(state));
#endif
                return false;
            }
#if PAL
            else
            {
                RbCursorProof.Change<T>(before, RbState.Labels(state));
            }
            Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
            Pal.Join(root == RbCursorSpec.Top(RbState.Labels(state)));
            Pal.Join(Pal.Implies(Pal.Returned(),
                RbAddSpec.Complete(comparer, keys.Value, key, root, RbState.Labels(state))));
            Pal.Join(Pal.Implies(!Pal.Returned(),
                order != 0 && RbCursorSpec.Same(RbState.Labels(state), before.Value)));
            RbCursorProof.Change<T>(RbState.Labels(state), before);
#endif
            if (Is4At(current))
            {
                Split4At(current);
#if PAL
                RbAddProof.Split(comparer, keys, key, before, current, parent, grandParent, greatGrandParent, oldOrder.Value, order);
                state = RbState.Split(state, current);
                RbCursorProof.Change<T>(RbLinkSpec.Replace(before.Value, current, RbSplitSpec.Split(RbLinkSpec.Sub(before.Value, current))),
                    RbState.Labels(state));
#endif
                if (IsRedAt(parent))
                {
#if PAL
                    Ghost<RbLabels<T>> split = RbState.Labels(state);
                    RbCursorProof.Change<T>(RbState.Labels(state), split);
                    RbAddProof.BalanceNodes(current, parent, grandParent, greatGrandParent, split);
#endif
                    root = InsertionBalance(root, current, ref parent, grandParent!, greatGrandParent);
#if PAL
                    state = RbState.Balance(state, current);
                    RbCursorProof.Change<T>(RbBalanceSpec.Balanced(split.Value, current), RbState.Labels(state));
#endif
                }
#if PAL
                Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
                Pal.Join(root == RbCursorSpec.Top(RbState.Labels(state)));
                Pal.Join(RbAddSpec.Ready(comparer, keys.Value, key, RbState.Labels(state), current, parent, grandParent, order, measure.Value));
#endif
            }
#if PAL
            else
            {
                RbCursorProof.Change<T>(before, RbState.Labels(state));
            }
            Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
            Pal.Join(root == RbCursorSpec.Top(RbState.Labels(state)));
            Pal.Join(RbAddSpec.Ready(comparer, keys.Value, key, RbState.Labels(state), current, parent, grandParent, order, measure.Value));
            Ghost<RbLabels<T>> after = RbState.Labels(state);
            RbCursorProof.Change<T>(RbState.Labels(state), after);
            RbCursorProof.Open(current, after);
#endif
            greatGrandParent = grandParent;
            grandParent = parent;
            parent = current;
            RbNode<T>? next = order < 0 ? current.left : current.right;
#if PAL
            RbCursorProof.Close(current, after);
            RbAddProof.Advance(comparer, keys, key, after, current, grandParent, greatGrandParent, next, order, measure.Value);
            RbCursorProof.Change<T>(after, RbState.Labels(state));
#endif
            current = next;
        }
#if PAL
        Ghost<RbLabels<T>> descentModel = RbState.Labels(state);
        RbCursorProof.Change<T>(RbState.Labels(state), descentModel);
        RbAddProof.AtEnd(comparer, keys, key, descentModel, parent, grandParent, greatGrandParent, order);
#endif
        RbNode<T> node = NewLeaf(key, true);
#if PAL
        RbCursorProof.Change<T>(RbSplitSpec.Color(RbLeafSpec.Leaf(node, key), true), RbLeafSpec.Leaf(node, key));
        RbLeafProof.Fresh(node, key, descentModel);
        RbAddProof.Linked(comparer, keys, key, descentModel, node, parent, grandParent, greatGrandParent, order);
#endif
        bool insertRight = order > 0;
        LinkLeaf(parent!, node, insertRight, key);
#if PAL
        state = RbState.Link(state, parent!, node, key, insertRight);
        RbCursorProof.Change<T>(RbLeafSpec.SetChild(descentModel.Value, parent!, insertRight, RbLeafSpec.Leaf(node, key)), RbState.Labels(state));
#endif
        if (IsRedAt(parent))
        {
#if PAL
            Ghost<RbLabels<T>> linked = RbState.Labels(state);
            RbCursorProof.Change<T>(RbState.Labels(state), linked);
            RbAddProof.BalanceNodes(node, parent, grandParent, greatGrandParent, linked);
#endif
            root = InsertionBalance(root, node, ref parent, grandParent!, greatGrandParent);
#if PAL
            state = RbState.Balance(state, node);
            RbCursorProof.Change<T>(RbBalanceSpec.Balanced(linked.Value, node), RbState.Labels(state));
#endif
        }
#if PAL
        Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
        Pal.Join(root == RbCursorSpec.Top(RbState.Labels(state)));
        Pal.Join(RbAddSpec.Ok(comparer, RbAddSpec.Expected(comparer, keys.Value, key), RbState.Labels(state)));
        Ghost<RbLabels<T>> final = RbState.Labels(state);
        RbCursorProof.Change<T>(RbState.Labels(state), final);
        RbAddProof.Finish(comparer, keys, key, final);
#endif
        ColorLocal(root!, false);
        return true;
    }
}
