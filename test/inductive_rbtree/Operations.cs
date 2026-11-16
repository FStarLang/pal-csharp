using System.Collections.Generic;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static partial class RbTree
{
    [Ensures("RbSpec.Holds(Result, SpecTree.Leaf<(T, bool)>())")]
    public static RbNode<T>? Empty<T>()
    {
        RbProof.Empty<T>();
        return null;
    }

    // Detach-clear: the old tree's ownership remains available to the caller.
    [Requires("RbSpec.Holds(root, tree)")]
    [Ensures("RbSpec.Holds(Result, SpecTree.Leaf<(T, bool)>())")]
    [Ensures("RbSpec.Holds(detached, tree)")]
    [Ensures("detached == root")]
    public static RbNode<T>? Clear<T>(RbNode<T>? root, out RbNode<T>? detached,
        Ghost<SpecTree<(T, bool)>> tree = default)
    {
        detached = root;
        return Empty<T>();
    }

    [Requires("RbSpec.Holds(root, tree)")]
    [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(tree))")]
    [Ensures("RbSpec.Holds(root, tree)")]
    [Ensures("Result == SpecSearchTree.Contains(comparer, tree, key)")]
    [Ensures("Result == (Pal.KeyIndex(comparer, SpecSearchTree.Keys(tree), key) >= 0)")]
    public static bool Contains<T>(RbNode<T>? root, T key, IComparer<T> comparer,
        Ghost<SpecTree<(T, bool)>> tree = default)
    {
        RbProof.ContainsKeys(comparer, tree, key);
        RbCursorProof.Label(root, tree);
        bool result = Search(root, key, comparer);
        RbCursorProof.Unlabel(root, tree);
        return result;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && root == RbCursorSpec.Top(nodes)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Result == SpecSearchTree.Contains(comparer, RbCursorSpec.Strip(nodes), key)")]
    private static bool Search<T>(RbNode<T>? root, T key, IComparer<T> comparer,
        Ghost<RbLabels<T>> nodes = default)
    {
        RbNode<T>? current = root;
        RbCursorProof.Root(nodes);
        while (current != null)
        {
#if PAL
            Pal.Decreases(RbCursorSpec.Lookup(nodes.Value, current).Size);
            Pal.Invariant(RbCursorSpec.Owns(nodes.Value));
            Pal.Invariant(current == null || RbCursorSpec.Member(nodes.Value, current));
            Pal.Invariant(SpecSearchTree.Contains(comparer, RbCursorSpec.Lookup(nodes.Value, current), key) ==
                SpecSearchTree.Contains(comparer, RbCursorSpec.Strip(nodes.Value), key));
            Pal.Invariant(Pal.Implies(Pal.Returned(),
                Pal.ReturnValue<bool>() &&
                SpecSearchTree.Contains(comparer, RbCursorSpec.Strip(nodes.Value), key)));
#endif
            RbCursorProof.Open(current!, nodes);
            T k = current!.key;
            int cmp = comparer.Compare(key, k);
            RbCursorProof.Close(current!, nodes);
            if (cmp == 0)
            {
                return true;
            }
            RbCursorProof.Open(current!, nodes);
            RbNode<T>? next = cmp < 0 ? current!.left : current!.right;
            RbCursorProof.Close(current!, nodes);
            current = next;
        }
        return false;
    }

    [Requires("RbSpec.Holds(root, tree)")]
    [Requires("tree.Size <= 2147483647")]
    [Ensures("RbSpec.Holds(root, tree)")]
    [Ensures("Result == tree.Size")]
    [Ensures("Result == SpecSearchTree.Keys(tree).Length")]
    [Decreases("tree")]
    public static int Count<T>(RbNode<T>? root, Ghost<SpecTree<(T, bool)>> tree = default)
    {
        RbProof.Cases(root, tree);
        if (root == null)
            return 0;
        RbProof.Open(root, tree);
        T k = root.key;
        bool red = root.red;
        RbNode<T>? l = root.left;
        RbNode<T>? r = root.right;
        int nl = Count(l);
        int nr = Count(r);
        RbProof.Close(root, k, red, l, r, RbSpec.Left(tree.Value), RbSpec.Right(tree.Value));
        return 1 + nl + nr;
    }
}
