using System.Collections.Generic;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static partial class RbTree
{
    // Iterative top-down insertion. A duplicate may reshape the search path.
    [Requires("RbSpec.Holds(root, tree)")]
    [Requires("SpecSearchTree.IsRedBlack(tree)")]
    [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(tree))")]
    [Ensures("RbAddSpec.Added(Result, comparer, tree, key)")]
    public static RbNode<T>? Add<T>(RbNode<T>? root, T key, IComparer<T> comparer,
        Ghost<SpecTree<(T, bool)>> tree = default)
    {
        RbCursorProof.Label(root, tree);
        RbNode<T>? result = AddTopDown(root, key, comparer);
        RbAddProof.Publish(result, comparer, key, tree);
        return result;
    }
}
