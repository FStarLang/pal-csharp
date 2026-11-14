using System.Collections.Generic;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static class RbClients
{
    [Ensures("RbSpec.Holds(Result, SpecTree.Leaf<(T, bool)>())")]
    [Ensures("RbSpec.Detached(detached)")]
    [Ensures("detached != null")]
    public static RbNode<T>? SingletonRoundTrip<T>(T key, IComparer<T> comparer,
        out RbNode<T>? detached)
    {
        RbNode<T>? root = RbTree.Empty<T>();
        root = RbTree.Add(root, key, comparer);
        bool found = RbTree.Contains(root, key, comparer);
        Pal.Assert(found);
        int one = RbTree.Count(root);
        Pal.Assert(one == 1);
        root = RbTree.Add(root, key, comparer);
        int stillOne = RbTree.Count(root);
        Pal.Assert(stillOne == 1);
        root = RbTree.Remove(root, key, comparer, out detached);
        int zero = RbTree.Count(root);
        Pal.Assert(zero == 0);
        return root;
    }

    [Requires("RbSpec.Holds(root, tree)")]
    [Ensures("RbSpec.Holds(detached, tree)")]
    [Ensures("RbAddSpec.Added(Result, comparer, SpecTree.Leaf<(T, bool)>(), key)")]
    public static RbNode<T>? ClearAndReuse<T>(RbNode<T>? root, T key, IComparer<T> comparer,
        out RbNode<T>? detached, Ghost<SpecTree<(T, bool)>> tree = default)
    {
        RbNode<T>? empty = RbTree.Clear(root, out detached);
        int zero = RbTree.Count(empty);
        Pal.Assert(zero == 0);
        return RbTree.Add(empty, key, comparer);
    }
}
