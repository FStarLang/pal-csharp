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

    /// <summary>The ring of <paramref name="n"/> nodes from <paramref name="hd"/> (null exactly when empty), whose nodes are exactly those <paramref name="h"/> says <paramref name="owner"/>, a non-null object, owns.</summary>
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

    /// <summary>A lemma: a node of the ring is held, and so are its neighbours, which are in the ring, non-null, right after and right before it (cyclically); it is first exactly when it is <paramref name="hd"/>, inserting before its next node puts the new node right after it, and the item at its position is its own.</summary>
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

    /// <summary>A lemma: the ring has <paramref name="n"/> nodes; when there are any, the first is <paramref name="hd"/>, held, at position 0, and the last is the one before it, at position <c>n - 1</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.ends")]
    public static void Ends<K>(SpecHeap<K> h, K? hd, SpecInt n) where K : class => throw Ghost();

    /// <summary>A lemma: a node of <paramref name="o"/>'s ring is held and owned by <paramref name="o"/>; the ring is not empty, and the node is its own next exactly when it is the only one, which is then <paramref name="hd"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.member")]
    public static void Member<K, O>(SpecHeap<K> h, K? hd, SpecInt n, K x, O o) where K : class where O : class => throw Ghost();

    /// <summary>A lemma: a node <paramref name="h"/> holds is owned by the owner of a ring exactly when it is in the ring.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.owns")]
    public static void Owns<K, O>(SpecHeap<K> h, K? hd, SpecInt n, K x, O o) where K : class where O : class => throw Ghost();

    /// <summary>
    /// A lemma: <paramref name="x"/>, removed from <paramref name="o"/>'s ring -- its neighbours
    /// linked to each other (unless it was alone), every other link and view kept, and
    /// <paramref name="x"/> left without an owner (<paramref name="h1"/>) -- leaves the ring
    /// entered at <paramref name="hd1"/> (null when it was alone, its next node when it was the
    /// first) as <paramref name="o"/>'s ring without <paramref name="x"/>, and its items without
    /// <paramref name="x"/>'s.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.removed")]
    public static void Removed<K, O>(SpecHeap<K> h0, SpecHeap<K> h1, K? hd, SpecInt n, K x, K? hd1, O o) where K : class where O : class => throw Ghost();

    /// <summary>
    /// The first position of <paramref name="s"/> whose element matches <paramref name="value"/>, or -1:
    /// when <paramref name="value"/> is null, a null element; otherwise one
    /// <c>EqualityComparer&lt;T&gt;.Default</c> calls equal to it (<see cref="Pal.DefaultEquals{T}"/>).
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.index_of")]
    public static SpecInt IndexOf<T>(Seq<T> s, T value) => throw Ghost();

    /// <summary>The first position at or after <paramref name="i"/> whose element matches <paramref name="value"/> (as in <see cref="IndexOf{T}"/>), or -1.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.index_from")]
    public static SpecInt IndexFrom<T>(Seq<T> s, T value, SpecInt i) => throw Ghost();

    /// <summary>The last position of <paramref name="s"/> whose element matches <paramref name="value"/> (as in <see cref="IndexOf{T}"/>), or -1.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.last_index_of")]
    public static SpecInt LastIndexOf<T>(Seq<T> s, T value) => throw Ghost();

    /// <summary>The last position at or before <paramref name="i"/> whose element matches <paramref name="value"/>, or -1.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.last_from")]
    public static SpecInt LastFrom<T>(Seq<T> s, T value, SpecInt i) => throw Ghost();

    /// <summary>A lemma: a forward search from <paramref name="i"/> (at least 0) is -1 past the end, <paramref name="i"/> when the element there matches, and the search from <c>i + 1</c> otherwise.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.find_step")]
    public static void FindStep<T>(Seq<T> s, T value, SpecInt i) => throw Ghost();

    /// <summary>A lemma: a backward search from <paramref name="i"/> (before the end) is -1 before 0, <paramref name="i"/> when the element there matches, and the search from <c>i - 1</c> otherwise.</summary>
    [SpecOp("Pulse.Lib.CSharp.RegionRing.last_step")]
    public static void LastStep<T>(Seq<T> s, T value, SpecInt i) => throw Ghost();

    /// <summary>A lemma: the node at position <paramref name="k"/> of the ring, when there is one, is held, non-null, and at <paramref name="k"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.at")]
    public static void At<K>(SpecHeap<K> h, K? hd, SpecInt n, SpecInt k) where K : class => throw Ghost();
    /// <summary>The node after <paramref name="x"/> (<c>LinkedListNode.Next</c>): its next link, or null when that is the ring's first node <paramref name="hd"/> again or <paramref name="x"/> is detached.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.succ")]
    public static K? Succ<K>(SpecHeap<K> h, K? hd, K x) where K : class => throw Ghost();

    /// <summary>The node before <paramref name="x"/> (<c>LinkedListNode.Previous</c>): its previous link, or null when <paramref name="x"/> is the first node <paramref name="hd"/> or is detached.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.pred")]
    public static K? Pred<K>(SpecHeap<K> h, K? hd, K x) where K : class => throw Ghost();

    /// <summary>A lemma: in a ring, <see cref="Succ{K}"/> and <see cref="Pred{K}"/> of a node at position <c>i</c> are the nodes at <c>i + 1</c> and <c>i - 1</c>, null past the ends.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.succ_at")]
    public static void SuccAt<K>(SpecHeap<K> h, K? hd, SpecInt n, K x) where K : class => throw Ghost();

    /// <summary>The first <paramref name="k"/> nodes of <paramref name="s"/> are detached at <paramref name="h"/> (links and owner null, items kept); every other node holds what it held at <paramref name="h0"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.cleared")]
    public static bool Cleared<K>(SpecHeap<K> h0, SpecHeap<K> h, Seq<K> s, SpecInt k) where K : class => throw Ghost();

    /// <summary>A lemma: nothing of the ring is cleared yet, and a nonempty ring's first node is at position 0.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.clear_start")]
    public static void ClearStart<K>(SpecHeap<K> h0, K? hd, SpecInt n) where K : class => throw Ghost();

    /// <summary>A lemma: the node at the end of a cleared prefix of <paramref name="o"/>'s ring is held, owned by <paramref name="o"/>, and its <see cref="Succ{K}"/> is the ring's next node (null after the last).</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.clear_next")]
    public static void ClearNext<K, O>(SpecHeap<K> h0, SpecHeap<K> h, K? hd, SpecInt n, K x, O o) where K : class where O : class => throw Ghost();

    /// <summary>A lemma: detaching the node at the end of a cleared prefix extends the prefix by one.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.clear_step")]
    public static void ClearStep<K>(SpecHeap<K> h0, SpecHeap<K> h1, SpecHeap<K> h2, K? hd, SpecInt n, K x) where K : class => throw Ghost();

    /// <summary>A lemma: <paramref name="o"/>'s ring cleared to its end leaves <paramref name="o"/> the empty ring.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.clear_done")]
    public static void ClearDone<K, O>(SpecHeap<K> h0, SpecHeap<K> h, K? hd, SpecInt n, O o) where K : class where O : class => throw Ghost();

    /// <summary>A lemma: a write that changes <paramref name="x"/>'s owner but not its links keeps the ring through it.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.reowned")]
    public static void Reowned<K>(SpecHeap<K> h1, SpecHeap<K> h2, K? hd, SpecInt n, K x) where K : class => throw Ghost();

    /// <summary>A lemma: a node of the heap with no owner, inserted into <paramref name="o"/>'s ring at <paramref name="k"/> and then given <paramref name="o"/> as its owner, is <paramref name="o"/>'s, with its item at <paramref name="k"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionRing.reattached")]
    public static void Reattached<K, O>(SpecHeap<K> h0, SpecHeap<K> h1, SpecHeap<K> h2, K? hd0, SpecInt n0, K? hd1, K nw, SpecInt k, O o) where K : class where O : class => throw Ghost();
}
