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
}
