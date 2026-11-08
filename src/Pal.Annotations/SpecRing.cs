using System;

namespace PalLang;

/// <summary>
/// R31.4. Rings: circular doubly-linked lists of a <c>[Region(Cyclic = true)]</c> class, each
/// owned by one object every node points back to (<c>LinkedList&lt;T&gt;</c>).
/// <c>Pulse.Lib.CSharp.RegionRing</c>. The first type argument of each
/// <see cref="RegionOpAttribute"/> member is the region class <c>K</c>, whose view is a pair of
/// its item and its owner; a <c>void</c> one is a lemma, called as a ghost statement.
/// </summary>
public static class SpecRing
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecRing is a specification-only construct and has no runtime meaning.");

    /// <summary>The ring of <paramref name="n"/> nodes from <paramref name="hd"/> (null exactly when empty), whose nodes are exactly those <paramref name="h"/> says <paramref name="owner"/> owns.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.ring")]
    public static bool Ring<K, O>(SpecHeap<K> h, K? hd, SpecInt n, O? owner) where K : class where O : class => throw Ghost();

    /// <summary>The ring of <paramref name="n"/> nodes from <paramref name="hd"/>, whoever owns it.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.shape")]
    public static bool Shape<K>(SpecHeap<K> h, K? hd, SpecInt n) where K : class => throw Ghost();

    /// <summary>The <paramref name="n"/> nodes reached from <paramref name="hd"/>, in order.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.nodes")]
    public static Seq<K> Nodes<K>(SpecHeap<K> h, K? hd, SpecInt n) where K : class => throw Ghost();

    /// <summary>The items of the nodes of <paramref name="s"/>, in order.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.items")]
    public static Seq<T> Items<K, T>(SpecHeap<K> h, Seq<K> s) where K : class => throw Ghost();

    /// <summary>The item of a node the heap holds.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.item")]
    public static T Item<K, T>(SpecHeap<K> h, K x) where K : class => throw Ghost();

    /// <summary>The owner a node points back to; null for a node the heap does not hold.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.owner")]
    public static O? Owner<K, O>(SpecHeap<K> h, K? x) where K : class where O : class => throw Ghost();

    /// <summary>The heap holds the same nodes, each with the same view.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.views_kept")]
    public static bool ViewsKept<K>(SpecHeap<K> h0, SpecHeap<K> h1) where K : class => throw Ghost();

    /// <summary><paramref name="x"/> has null links and no owner and keeps its item; every other node is as it was.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.detached")]
    public static bool Detached<K>(SpecHeap<K> h0, SpecHeap<K> h1, K x) where K : class => throw Ghost();

    /// <summary>The position of <paramref name="x"/> in <paramref name="s"/> (by reference), or -1.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.pos")]
    public static SpecInt Pos<K>(Seq<K> s, K? x) where K : class => throw Ghost();

    /// <summary>Where inserting before <paramref name="node"/> puts the new node: its position, or the end when it is the first.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.ins_index")]
    public static SpecInt InsIndex<K>(Seq<K> s, K? node) where K : class => throw Ghost();

    /// <summary><paramref name="s"/> with <paramref name="x"/> inserted at <paramref name="i"/> (unchanged out of range).</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.insert_at")]
    public static Seq<T> InsertAt<T>(Seq<T> s, SpecInt i, T x) => throw Ghost();

    /// <summary><paramref name="s"/> without its element at <paramref name="i"/> (unchanged out of range).</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.remove_at")]
    public static Seq<T> RemoveAt<T>(Seq<T> s, SpecInt i) => throw Ghost();

    /// <summary>A lemma: a node of the ring is held, and so are its neighbours, which are in the ring.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.neighbours")]
    public static void Neighbours<K>(SpecHeap<K> h, K? hd, SpecInt n, K x) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: <paramref name="nw"/>, held but not in the ring, linked in before
    /// <paramref name="node"/> in three writes -- <paramref name="nw"/>'s links
    /// (<paramref name="h1"/>), the next link of the node before <paramref name="node"/>
    /// (<paramref name="h2"/>), <paramref name="node"/>'s previous link (<paramref name="h3"/>),
    /// each keeping every view -- makes the ring one longer, with <paramref name="nw"/> at
    /// <see cref="InsIndex"/>.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.inserted3")]
    public static void Inserted<K>(SpecHeap<K> h0, SpecHeap<K> h1, SpecHeap<K> h2, SpecHeap<K> h3, K? hd, SpecInt n, K node, K nw) where K : class => throw Ghost();

    /// <summary>A lemma: <paramref name="nw"/>, its links both set to itself (<paramref name="h1"/>, its view kept), is the ring of one, which is the empty ring of <paramref name="hd"/> with it inserted at 0.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.single")]
    public static void Single<K>(SpecHeap<K> h0, SpecHeap<K> h1, K? hd, SpecInt n, K nw) where K : class => throw Ghost();

    /// <summary>A lemma: <paramref name="nw"/>, allocated into <paramref name="h0"/> giving <paramref name="ha"/>, is not in the ring, which with its items is unchanged.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.allocated")]
    public static void Allocated<K>(SpecHeap<K> h0, SpecHeap<K> ha, K? hd, SpecInt n, K nw) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: <paramref name="nw"/>, allocated owned by <paramref name="o"/> (<paramref name="ha"/>),
    /// then inserted at <paramref name="k"/> into <paramref name="o"/>'s ring keeping every view
    /// (<paramref name="h1"/>), makes <paramref name="o"/>'s ring one longer, with its item at <paramref name="k"/>.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.adopted")]
    public static void Adopted<K, O>(SpecHeap<K> h0, SpecHeap<K> ha, SpecHeap<K> h1, K? hd0, SpecInt n0, K? hd1, K nw, SpecInt k, O o) where K : class where O : class => throw Ghost();

    /// <summary>A lemma: the ring with <paramref name="nw"/> last, entered at <paramref name="nw"/>, has it first.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.rotated")]
    public static void Rotated<K>(SpecHeap<K> h, K? hd, SpecInt n, Seq<K> s0, K nw) where K : class => throw Ghost();

    /// <summary>A lemma: inserting before the first node of a nonempty ring puts the new node last.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.ins_head")]
    public static void InsHead<K>(SpecHeap<K> h, K? hd, SpecInt n) where K : class => throw Ghost();

    /// <summary>A lemma: the ring has <paramref name="n"/> nodes; when there are any, the first is <paramref name="hd"/>, held, and the last is the one before it.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.ends")]
    public static void Ends<K>(SpecHeap<K> h, K? hd, SpecInt n) where K : class => throw Ghost();
}
