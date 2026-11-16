using PalLang;

// Lemmas for SortedSet<T>'s merges (UnionWith, IntersectWith).
[assembly: IncludePulseFile("SortedSetMerge.fst")]

namespace System.Collections.Generic
{
    // `SortedSetMerge.fst`. A `[SpecOp]` lemma rather than a C# `[Lemma]`: a call of the latter
    // in a loop counts as one that may change the receiver's nodes (R27.16), which would make
    // the merge loops carry the receiver at a fresh model.
    internal static class SortedSetMerge
    {
        private static Exception Ghost() => new InvalidOperationException(
            "SortedSetMerge is a specification-only construct and has no runtime meaning.");

        // `p` is the suffix of `s` of its length (opaque to the solver; see `SortedSetMerge.fst`).
        [SpecOp("SortedSetMerge.suffix")]
        internal static bool Suffix<T>(Seq<T> s, Seq<T> p) => throw Ghost();

        // `s[i..]` and `s[..j]` without bounds to prove (empty out of range).
        [SpecOp("SortedSetMerge.drop")]
        internal static Seq<T> Drop<T>(Seq<T> s, SpecInt i) => throw Ghost();

        [SpecOp("SortedSetMerge.take")]
        internal static Seq<T> Take<T>(Seq<T> s, SpecInt j) => throw Ghost();

        // The whole of `s` is a suffix of `s`. Called on a fresh enumerator's items.
        [SpecOp("SortedSetMerge.suffix_whole")]
        internal static void Whole<T>(Seq<T> s) => throw Ghost();

        // An enumerator over `s` whose pending items `p0` are a suffix of `s`: what holds of the
        // pending items `MoveNext` leaves, stated as the merge loops' invariants state it.
        // Called before the `MoveNext`.
        [SpecOp("SortedSetMerge.pending_next")]
        internal static void PendingNext<T>(Seq<T> s, Seq<T> p0) => throw Ghost();
    }
}
