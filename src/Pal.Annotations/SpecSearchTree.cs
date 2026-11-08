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

    /// <summary>
    /// R32.14. The subtree rooted at the node the top-down range search over <paramref name="tree"/>
    /// stops at, or the empty tree: the tree a view of the set searches.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.range_root")]
    public static SpecTree<(T, TTag)> RangeRoot<T, TTag>(IComparer<T> comparer, SpecTree<(T, TTag)> tree, T lower, T upper, bool lowerActive, bool upperActive) =>
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

    /// <summary>R27.16. The root of a colour-tagged tree is red (a leaf is not).</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.is_red")]
    public static bool IsRed<T>(SpecTree<(T, bool)> tree) => throw Ghost();

    /// <summary>R27.16. The tree with its root's colour set to red or black.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.recolor")]
    public static SpecTree<(T, bool)> Recolor<T>(SpecTree<(T, bool)> tree, bool red) => throw Ghost();

    /// <summary>R27.16. The root's right child made the root.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rot_left")]
    public static SpecTree<TItem> RotateLeft<TItem>(SpecTree<TItem> tree) => throw Ghost();

    /// <summary>R27.16. The root's left child made the root.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rot_right")]
    public static SpecTree<TItem> RotateRight<TItem>(SpecTree<TItem> tree) => throw Ghost();

    /// <summary>R27.16. The left child rotated left, then the root rotated right.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rot_left_right")]
    public static SpecTree<TItem> RotateLeftRight<TItem>(SpecTree<TItem> tree) => throw Ghost();

    /// <summary>R27.16. The right child rotated right, then the root rotated left.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rot_right_left")]
    public static SpecTree<TItem> RotateRightLeft<TItem>(SpecTree<TItem> tree) => throw Ghost();

    /// <summary>R27.16. A 4-node split: the root red, its children black.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.split4")]
    public static SpecTree<(T, bool)> Split4<T>(SpecTree<(T, bool)> tree) => throw Ghost();

    /// <summary>R27.16. Two 2-nodes merged: the root black, its children red.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.merge2")]
    public static SpecTree<(T, bool)> Merge2<T>(SpecTree<(T, bool)> tree) => throw Ghost();

    /// <summary>
    /// R27.17. <c>Node.Rotate</c>'s tree: a single rotation also blackens the red grandchild
    /// it lifts. <paramref name="rotation"/> is a <c>[SpecType]</c> enum whose image is
    /// <c>SearchTree.tree_rotation</c>.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rotate")]
    public static SpecTree<(T, bool)> Rotate<TRotation, T>(TRotation rotation, SpecTree<(T, bool)> tree) => throw Ghost();

    /// <summary>R27.17. The grandchild a rotation lifts is red.</summary>
    [SpecOp("Pulse.Lib.CSharp.SearchTree.can_rotate")]
    public static bool CanRotate<TRotation, T>(TRotation rotation, SpecTree<(T, bool)> tree) => throw Ghost();

    /// <summary>
    /// R27.32. The red-black tree built from <paramref name="items"/>[lo..hi] by halving, with
    /// <paramref name="red"/> (a saved red leaf, or a leaf) under its leftmost node.
    /// <c>Pulse.Lib.CSharp.SortedBuild</c>.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SortedBuild.build")]
    public static SpecTree<(T, bool)> Build<T>(Seq<T> items, SpecInt lo, SpecInt hi, SpecTree<(T, bool)> red) =>
        throw Ghost();

    /// <summary>R27.32. A leaf, or a single red node: what <see cref="Build{T}"/> takes as its saved node.</summary>
    [SpecOp("Pulse.Lib.CSharp.SortedBuild.red_arg")]
    public static bool IsRedLeaf<T>(SpecTree<(T, bool)> tree) => throw Ghost();

    /// <summary>
    /// R27.32. A lemma: <paramref name="root"/>, linked in <paramref name="h3"/> to its left
    /// subtree and re-linking <paramref name="red"/> since <paramref name="h0"/>, stays so when
    /// its right child is then set to the root of a tree new since <paramref name="h3"/>.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.SortedBuild.link_right")]
    public static void LinkRight<K, T>(SpecHeap<K> h0, SpecHeap<K> h3, K? red, K? root) where K : class => throw Ghost();

    /// <summary>
    /// R27.32. A lemma: one step of <see cref="Build{T}"/> on a slice of at least four items, split at <paramref name="mid"/> with parity <paramref name="even"/>.
    /// It names a region class <typeparamref name="K"/> only to be a <c>[RegionOp]</c> lemma.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.SortedBuild.build_split")]
    public static void BuildSplit<K, T>(Seq<T> items, SpecInt lo, SpecInt hi, SpecInt mid, bool even, SpecTree<(T, bool)> red) where K : class => throw Ghost();
}
