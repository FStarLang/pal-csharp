using System;

namespace PalLang;

/// <summary>
/// R27.43. A copy of a region's tree into fresh boxes of the region, built top-down from a
/// stack of (source, target) pairs (<c>SortedSet&lt;T&gt;.Node.DeepClone</c>).
/// <c>Pulse.Lib.CSharp.RegionClone</c>. The first type argument of each
/// <see cref="RegionOpAttribute"/> member is the <c>[Region]</c> class; a <c>void</c> one is a
/// lemma, called as a ghost statement. <c>h0</c> is the heap the copy started from and
/// <c>x</c> the root of the tree it copies; <c>root</c> is the copy's root and
/// <c>stack</c> the pairs still to be copied (top last).
/// </summary>
public static class SpecClone
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecClone is a specification-only construct and has no runtime meaning.");

    /// <summary>
    /// The loop invariant: the copy at <paramref name="root"/> in <paramref name="h"/> is the
    /// part of the source tree walked so far, in fresh boxes with the source's views; each
    /// pair on the stack still has both links null, and every other copied node links
    /// exactly where its source does.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RegionClone.cloning_at")]
    public static bool Cloning<K>(SpecHeap<K> h0, K x, SpecHeap<K> h, K root, Seq<(K, K)> stack) where K : class => throw Ghost();

    /// <summary>The loop's measure: twice the nodes not yet copied, plus the stack's length.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionClone.measure")]
    public static SpecInt Measure<K>(SpecHeap<K> h0, K x, SpecHeap<K> h, K root, Seq<(K, K)> stack) where K : class => throw Ghost();

    /// <summary>A lemma: a copy of the root alone, with the empty stack, pushed as the first pair.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionClone.init")]
    public static void Init<K>(SpecHeap<K> h0, K x, SpecHeap<K> h, K root, Seq<(K, K)> stack) where K : class => throw Ghost();

    /// <summary>A lemma: the pair <paramref name="next"/> popped off <paramref name="stack"/>; its source is a node with mapped children, its target a fresh node with null links.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionClone.pop")]
    public static void Pop<K>(SpecHeap<K> h0, K x, SpecHeap<K> h, K root, Seq<(K, K)> stack, (K, K) next) where K : class => throw Ghost();

    /// <summary>
    /// A lemma: the child on side <paramref name="left"/> of <paramref name="next"/>'s source
    /// (in <paramref name="h"/>), copied to <paramref name="copy"/> (heap <paramref name="h1"/>)
    /// and linked under its target (heap <paramref name="h2"/>), to be pushed onto
    /// <paramref name="stack"/>.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.RegionClone.link")]
    public static void Link<K>(bool left, SpecHeap<K> h0, K x, SpecHeap<K> h, SpecHeap<K> h1, SpecHeap<K> h2, K root, Seq<(K, K)> stack, (K, K) next, K copy) where K : class => throw Ghost();

    /// <summary>A lemma: <paramref name="next"/> is done once each of its target's null links is null in its source.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionClone.done_")]
    public static void Done<K>(SpecHeap<K> h0, K x, SpecHeap<K> h, K root, Seq<(K, K)> stack, (K, K) next) where K : class => throw Ghost();

    /// <summary>A lemma: with the stack empty, the copy is an unshared tree of fresh boxes with the source's view tree.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionClone.finish")]
    public static void Finish<K>(SpecHeap<K> h0, K x, SpecHeap<K> h, K root, Seq<(K, K)> stack) where K : class => throw Ghost();
}
