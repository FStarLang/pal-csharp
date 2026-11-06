using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// The comparer-directed searches of a <see cref="SpecTree{T}"/> of keyed, tagged nodes:
/// a red-black tree's model, each node its key and its colour (doc/translation.md R27.9).
/// Each follows the path the code's own search follows, so none needs an ordering
/// hypothesis. <c>Pulse.Lib.CSharp.SearchTree</c>.
/// </summary>
public static class SpecSearchTree
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecSearchTree is a specification-only construct and has no runtime meaning.");

    /// <summary>Whether the search for <paramref name="item"/> ends at a node.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.contains")]
    public static bool Contains<T, TTag>(IComparer<T> comparer, SpecTree<(T, TTag)> tree, T item) =>
        throw Ghost();

    /// <summary>The key the search ends at, or <paramref name="fallback"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.find")]
    public static T Find<T, TTag>(IComparer<T> comparer, SpecTree<(T, TTag)> tree, T item, T fallback) =>
        throw Ghost();

    /// <summary>R27.13. The key at the root, or <paramref name="fallback"/> in the empty tree.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.root_key")]
    public static T RootKey<T, TTag>(SpecTree<(T, TTag)> tree, T fallback) => throw Ghost();

    /// <summary>The leftmost key, or <paramref name="fallback"/> in the empty tree.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.leftmost")]
    public static T Leftmost<T, TTag>(SpecTree<(T, TTag)> tree, T fallback) => throw Ghost();

    /// <summary>The rightmost key, or <paramref name="fallback"/> in the empty tree.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rightmost")]
    public static T Rightmost<T, TTag>(SpecTree<(T, TTag)> tree, T fallback) => throw Ghost();

    /// <summary>
    /// The breadth-first position of the node the search ends at, the subtree's root being
    /// <paramref name="start"/>, or -1.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.heap_index")]
    public static SpecInt HeapIndex<T, TTag>(IComparer<T> comparer, SpecTree<(T, TTag)> tree, T item, SpecInt start) =>
        throw Ghost();

    /// <summary>R27.14. <c>2^height</c>: a breadth-first position in the tree is below <c>Breadth - 1</c>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.breadth")]
    public static SpecInt Breadth<TItem>(SpecTree<TItem> tree) => throw Ghost();

    /// <summary>
    /// R27.14. A search for a breadth-first position starting at <paramref name="start"/> in
    /// <paramref name="tree"/>, inside a tree of height <paramref name="height"/>, stays at most
    /// <c>2^(height+1) - 2</c>.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.index_room")]
    public static bool IndexRoom<TItem>(SpecInt start, SpecTree<TItem> tree, SpecInt height) => throw Ghost();

    /// <summary>R27.14. <paramref name="item"/> is within the bounds that are active.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.in_range")]
    public static bool InRange<T>(IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, T item) =>
        throw Ghost();

    /// <summary>R27.14. Some item of <paramref name="items"/> is within the bounds that are active.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.any_in_range")]
    public static bool AnyInRange<T>(IComparer<T> comparer, Seq<T> items, T lower, T upper, bool lowerActive, bool upperActive) =>
        throw Ghost();

    /// <summary>R27.14. The top-down range search over <paramref name="tree"/> stops at a node.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.range_hit")]
    public static bool RangeHit<T, TTag>(IComparer<T> comparer, SpecTree<(T, TTag)> tree, T lower, T upper, bool lowerActive, bool upperActive) =>
        throw Ghost();

    /// <summary>R27.11. The keys in order: the set a search tree holds once they are strictly sorted.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.keys")]
    public static Seq<T> Keys<T, TTag>(SpecTree<(T, TTag)> tree) => throw Ghost();

    /// <summary>
    /// R27.11. A red-black tree, each node tagged with whether it is red: no red node has a
    /// red child, every path has the same number of black nodes, and the root is black.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.red_black")]
    public static bool IsRedBlack<T>(SpecTree<(T, bool)> tree) => throw Ghost();
}
