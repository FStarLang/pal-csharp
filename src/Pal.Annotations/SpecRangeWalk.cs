using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R35.14. A range-pruned in-order walk of a region's search tree
/// (<c>SortedSet&lt;T&gt;.TreeSubSet</c>'s <c>InOrderTreeWalk</c>): R27.35's walk, which pushes
/// only nodes within the bounds and moves past the others towards the range.
/// <c>Pulse.Lib.CSharp.RangeWalk</c>. The first type argument of each
/// <see cref="RegionOpAttribute"/> member is the <c>[Region]</c> class; a <c>void</c> member is
/// a lemma, called as a ghost statement.
/// </summary>
public static class SpecRangeWalk
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecRangeWalk is a specification-only construct and has no runtime meaning.");

    /// <summary>The items of <paramref name="items"/> within the active bounds, in order.</summary>
    [SpecOp("Pulse.Lib.CSharp.RangeWalk.filter")]
    public static Seq<T> Filter<T>(IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, Seq<T> items) => throw Ghost();

    /// <summary>
    /// A lemma: the range search's subtree of a sorted tree holds the tree's in-range keys, is
    /// sorted, and is no larger than the tree.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.RangeWalk.range_root_filter")]
    public static void RootFilter<T, TTag>(IComparer<T> comparer, SpecTree<(T, TTag)> tree, T lower, T upper, bool lowerActive, bool upperActive) => throw Ghost();

    /// <summary>Every pointer on the stack holds an in-range key over a strictly sorted subtree.</summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.rwalkable")]
    public static bool Walkable<K, T>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, Seq<K> stack) where K : class => throw Ghost();

    /// <summary>A lemma: the empty stack is walkable, range-walkable, and owes nothing.</summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.rwalkable_empty")]
    public static void Empty<K, T>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, Seq<K> stack) where K : class => throw Ghost();

    /// <summary>A lemma: pushing an in-range <paramref name="x"/> over a sorted subtree keeps the stack range-walkable.</summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.push")]
    public static void Push<K, T>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, Seq<K> stack, K? x) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: at <paramref name="x"/> under the active lower bound, the in-range keys of
    /// its tree followed by <paramref name="rest"/> are those of its right child's.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.skip_right")]
    public static void SkipRight<K, T>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, K? x, Seq<T> rest) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: at <paramref name="x"/> outside the range and not under its lower bound, the
    /// in-range keys of its tree followed by <paramref name="rest"/> are those of its left
    /// child's.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.skip_left")]
    public static void SkipLeft<K, T>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, K? x, Seq<T> rest) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: the top of a range-walkable stack whose in-range keys are the window
    /// <paramref name="keys"/>[<paramref name="n"/>..] has the key
    /// <paramref name="keys"/>[<paramref name="n"/>], and its right child's tree and the rest
    /// of the stack owe <paramref name="keys"/>[<paramref name="n"/>+1..].
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.pop_at")]
    public static void PopAt<K, T>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, Seq<K> stack, Seq<T> keys, SpecInt n) where K : class => throw Ghost();

    // R35.14. The view's breadth-first walk, which queues only the children the range may reach.

    /// <summary>Every pointer in the queue is a node over a strictly sorted subtree.</summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.rqueue")]
    public static bool Queue<K, T>(SpecHeap<K> h, IComparer<T> comparer, Seq<K> queue) where K : class => throw Ghost();

    /// <summary>
    /// The queue after one round of the view's walk: <paramref name="queue"/>'s rest, then its
    /// front's left child unless it is null or the front is at or under the active lower
    /// bound, then its right child unless it is null or the front is at or over the active
    /// upper bound.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.rbf_next")]
    public static Seq<K> BfNext<K, T>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, Seq<K> queue) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: a queue holding just a sorted subtree whose in-range keys are
    /// <paramref name="keys"/>, with an empty trace, starts a visit of <paramref name="keys"/>.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.rbf_start")]
    public static void BfStart<K, T, X>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, Seq<K> queue, Seq<T> keys, Seq<((T, X), bool)> tr) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: one round of the view's walk — dequeue the front, call the callback on it if
    /// it is in range, queue <see cref="BfNext"/> — owes strictly less, keeps the visit
    /// unless an in-range call returned false, and ends the walk when one did.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RangeWalk.rbf_dequeue")]
    public static void BfDequeue<K, T, X>(SpecHeap<K> h, IComparer<T> comparer, T lower, T upper, bool lowerActive, bool upperActive, Seq<K> queue, Seq<T> keys, Seq<((T, X), bool)> tr) where K : class => throw Ghost();
}
