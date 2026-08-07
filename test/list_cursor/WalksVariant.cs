using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant: the same three operations, written differently. Nothing here required a
/// translator change, which is the point — a cursor is not a shape the emitter recognises,
/// it is the ordinary loop rule applied to an invariant that happens to own something.
///
/// <para>The renderings that differ: <c>for</c> in place of <c>while</c>, an inequality
/// guard in place of a null test, the two field reads in the other order, a prefix
/// increment in the step position, an <c>if</c>-free early exit replaced by an exact-count
/// loop, and every local named differently.</para>
/// </summary>
public static class WalksVariant
{
    /// <summary>Prepending, with the allocation and the lemma call the other way round —
    /// the lemma names the node it is about, so it does not care.</summary>
    [Requires("Chain.Whole(rest, ys)")]
    [Ensures("Chain.Whole(Result, SpecList.Cons(item, ys))")]
    public static Cell<T>? Cons<T>(T item, Cell<T>? rest, Ghost<SpecList<T>> ys = default)
    {
        Cell<T> fresh = new Cell<T> { next = rest, value = item };
        ChainProof.Push(fresh, item, rest, ys);
        return fresh;
    }

    /// <summary>Counting with a <c>for</c> loop, whose counter is the split point.</summary>
    [Requires("Chain.Whole(start, ys)")]
    [Requires("ys.Length < 2147483647")]
    [Ensures("Chain.Whole(start, ys)")]
    [Ensures("Result == ys.Length")]
    public static int Length<T>(Cell<T>? start, Ghost<SpecList<T>> ys = default)
    {
        ChainProof.Start(start, ys);
        Cell<T>? walk = start;
        int seen = 0;
        for (; walk != null; ++seen)
        {
            Pal.Invariant(Chain.Seg(start, walk, SpecList.Take(ys.Value, seen)));
            Pal.Invariant(Chain.Whole(walk, SpecList.Drop(ys.Value, seen)));
            Pal.Invariant(seen >= 0 && ys.Value.Length >= seen);
            Pal.Invariant(ys.Value.Length < 2147483647);
            Pal.Decreases(ys.Value.Length - seen);

            ChainProof.AtEnd(walk, seen, ys);
            ChainProof.Open(walk, walk!, SpecList.Drop(ys.Value, seen));
            Cell<T>? onward = walk.next;
            T here = walk.value;
            ChainProof.Advance(start, walk, walk!, here, onward, seen, ys);
            walk = onward;
        }
        ChainProof.Finish(start, walk, seen, ys);
        return seen;
    }

    /// <summary>
    /// Indexing, with the loop stopping one short of the wanted cell and the final step
    /// spelled out afterwards. The guard is an inequality rather than a comparison, and the
    /// cursor is never null-tested at all — <c>AtEnd</c> supplies what the reads need.
    /// </summary>
    [Requires("Chain.Whole(start, ys)")]
    [Requires("k >= 0 && ys.Length > k && ys.Length < 2147483647")]
    [Ensures("Chain.Whole(start, ys)")]
    [Ensures("Pal.Same(Result, ys[k])")]
    public static T Nth<T>(Cell<T>? start, int k, Ghost<SpecList<T>> ys = default)
    {
        ChainProof.Start(start, ys);
        Cell<T>? walk = start;
        int passed = 0;
        while (passed != k)
        {
            Pal.Invariant(Chain.Seg(start, walk, SpecList.Take(ys.Value, passed)));
            Pal.Invariant(Chain.Whole(walk, SpecList.Drop(ys.Value, passed)));
            Pal.Invariant(passed >= 0 && k >= passed);
            Pal.Invariant(ys.Value.Length > k && ys.Value.Length < 2147483647);
            Pal.Decreases(k - passed);

            ChainProof.AtEnd(walk, passed, ys);
            ChainProof.Open(walk, walk!, SpecList.Drop(ys.Value, passed));
            Cell<T>? onward = walk!.next;
            T here = walk!.value;
            ChainProof.Advance(start, walk, walk!, here, onward, passed, ys);
            walk = onward;
            passed = passed + 1;
        }

        ChainProof.AtEnd(walk, passed, ys);
        ChainProof.Open(walk, walk!, SpecList.Drop(ys.Value, passed));
        Cell<T>? tail = walk!.next;
        T wanted = walk!.value;
        ChainProof.Advance(start, walk, walk!, wanted, tail, passed, ys);
        ChainProof.Close(start, tail, passed + 1, ys);
        return wanted;
    }
}
