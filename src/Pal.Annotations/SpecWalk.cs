using System;

namespace PalLang;

/// <summary>
/// R27.35. An in-order walk of a region's tree that keeps a stack of pointers into the
/// region (<c>SortedSet&lt;T&gt;</c>'s enumerator and <c>InOrderTreeWalk</c>). The stack is a
/// <see cref="Seq{T}"/> of node pointers; what it still owes is a pure function of the heap.
/// <c>Pulse.Lib.CSharp.RegionWalk</c>. The first type argument of each
/// <see cref="RegionOpAttribute"/> member is the <c>[Region]</c> class; a <c>void</c> one is a
/// lemma, called as a ghost statement. <c>reverse</c> walks from the right.
/// </summary>
public static class SpecWalk
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecWalk is a specification-only construct and has no runtime meaning.");

    /// <summary>The keys of <paramref name="tree"/> in order, or in reverse order.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionWalk.okeys")]
    public static Seq<T> Keys<T, TTag>(bool reverse, SpecTree<(T, TTag)> tree) => throw Ghost();

    /// <summary>The keys the stack still owes in <paramref name="h"/>, its top (last) entry first.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionWalk.pending")]
    public static Seq<T> Pending<K, T>(bool reverse, SpecHeap<K> h, Seq<K> stack) where K : class => throw Ghost();

    /// <summary>Every pointer on the stack is non-null and well-formed in <paramref name="h"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionWalk.walkable")]
    public static bool Walkable<K, T>(SpecHeap<K> h, Seq<K> stack) where K : class => throw Ghost();

    /// <summary>A lemma: the empty stack owes nothing and is walkable.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionWalk.pending_empty")]
    public static void Empty<K, T>(bool reverse, SpecHeap<K> h, Seq<K> stack) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: pushing the well-formed <paramref name="x"/> and moving to its near child
    /// (left, or right in reverse) keeps the keys still owed.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RegionWalk.descend")]
    public static void Descend<K, T>(bool reverse, SpecHeap<K> h, Seq<K> stack, K? x) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: the top of a non-empty walkable stack owes its own key first, then the keys
    /// of its far child's tree, then what the rest of the stack owes.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RegionWalk.pop")]
    public static void Pop<K, T>(bool reverse, SpecHeap<K> h, Seq<K> stack) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: <see cref="Pop{K, T}"/>, for a stack that owes the window
    /// <paramref name="keys"/>[<paramref name="n"/>..]: the top's key is
    /// <paramref name="keys"/>[<paramref name="n"/>], and its far child's tree and the rest of
    /// the stack owe <paramref name="keys"/>[<paramref name="n"/>+1..].
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RegionWalk.pop_at")]
    public static void PopAt<K, T>(bool reverse, SpecHeap<K> h, Seq<K> stack, Seq<T> keys, SpecInt n) where K : class => throw Ghost();

    /// <summary>A lemma: a walkable stack owes at least one key per pointer.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionWalk.walkable_length")]
    public static void Length<K, T>(bool reverse, SpecHeap<K> h, Seq<K> stack) where K : class => throw Ghost();

    // R27.39. The trace of a walk's callback (Pal.Trace): each entry is the view of the node
    // the callback was called on and what it returned.

    /// <summary>The callback was called on <paramref name="keys"/>[0..|tr|), in order, and returned true each time.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionWalk.visited")]
    public static bool Visited<T, X>(Seq<T> keys, Seq<((T, X), bool)> tr) => throw Ghost();

    /// <summary>
    /// A walk over <paramref name="keys"/> that returned <paramref name="res"/>: the callback was
    /// called on a prefix of the keys, in order, returned true on all calls but possibly the
    /// last, and the walk returned true exactly when it went through every key.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.RegionWalk.walked")]
    public static bool Walked<T, X>(Seq<T> keys, Seq<((T, X), bool)> tr, bool res) => throw Ghost();

    /// <summary>
    /// The protocol of a callback copying keys into an array from <paramref name="i0"/> up to
    /// <paramref name="hi"/>, starting from contents <paramref name="a0"/>, its cursor now at
    /// <paramref name="idx"/>.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.RegionWalk.copied")]
    public static bool Copied<T, X>(Seq<((T, X), bool)> tr, Seq<T> a0, Seq<T> a, SpecInt i0, SpecInt hi, SpecInt idx) => throw Ghost();

    /// <summary><paramref name="a"/> is <paramref name="a0"/> with the first min(|keys|, hi - i0) keys at <paramref name="i0"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionWalk.copy_result")]
    public static bool CopyResult<T>(Seq<T> keys, Seq<T> a0, Seq<T> a, SpecInt i0, SpecInt hi) => throw Ghost();
}
