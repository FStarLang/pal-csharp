using System.Collections.Generic;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static partial class RbTree
{
    // Iterative top-down deletion. A miss may reshape the search path.
    // A hit returns ownership of the physically detached matching node.
    [Requires("RbSpec.Holds(root, tree)")]
    [Requires("SpecSearchTree.IsRedBlack(tree)")]
    [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(tree))")]
    [Ensures("RbRemoveSpec.Removed(Result, comparer, tree, key)")]
    [Ensures("RbSpec.Detached(removed)")]
    [Ensures("Pal.Iff(removed == null, !SpecSearchTree.Contains(comparer, tree, key))")]
    public static RbNode<T>? Remove<T>(RbNode<T>? root, T key, IComparer<T> comparer,
        out RbNode<T>? removed, Ghost<SpecTree<(T, bool)>> tree = default)
    {
        RbCursorProof.Label(root, tree);
        RbNode<T>? result = RemoveTopDown(root, key, comparer, out removed);
        RbRemoveProof.Publish(result, comparer, key, tree);
        return result;
    }
}
