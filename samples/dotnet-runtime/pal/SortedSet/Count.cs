using PalLang;

// Lemmas for SortedSet<T>.CheckUniqueAndUnfoundElements as dotnet/runtime#133116 rewrites it
// (doc/translation.md §37).
[assembly: IncludePulseFile("SortedSetCount.fst")]

// R37.3. Called only in the growth branch, which the proof shows dead.
[assembly: SpecBinding("M:System.Numerics.BitOperations.RoundUpToPowerOf2(System.UInt32)", "SortedSetCount.round_up_pow2")]

namespace System.Collections.Generic
{
    internal static class SortedSetCount
    {
        private static Exception Ghost() => new InvalidOperationException(
            "SortedSetCount is a specification-only construct and has no runtime meaning.");

        // What the method is to count: the distinct keys of `ks` that `s` holds, and the items
        // of `s` that are not keys. A set admits every key; a view, the keys within its range.
        [SpecOp("SortedSetCount.found_all")]
        internal static SpecInt FoundAll<T>(IComparer<T> c, Seq<T> ks, Seq<T> s) => throw Ghost();

        [SpecOp("SortedSetCount.unfound_all")]
        internal static SpecInt UnfoundAll<T>(IComparer<T> c, Seq<T> ks, Seq<T> s) => throw Ghost();

        [SpecOp("SortedSetCount.found_range")]
        internal static SpecInt FoundRange<T>(IComparer<T> c, T lo, T hi, bool la, bool ua, Seq<T> ks, Seq<T> s) => throw Ghost();

        [SpecOp("SortedSetCount.unfound_range")]
        internal static SpecInt UnfoundRange<T>(IComparer<T> c, T lo, T hi, bool la, bool ua, Seq<T> ks, Seq<T> s) => throw Ghost();

        // `FindRange`'s `level`: the depth of the node the range search stops at.
        [SpecOp("SortedSetCount.range_depth")]
        internal static SpecInt RangeDepth<T, TTag>(IComparer<T> c, SpecTree<(T, TTag)> t, T lo, T hi, bool la, bool ua) => throw Ghost();

        // The method's range, as its body names it at the set and at a view (R37.7): a bound is
        // a sequence, empty for the set (which has no bound and no key to name one by) and
        // `One(_min)` or `One(_max)` for a view.
        [SpecOp("SortedSetCount.none")]
        internal static Seq<T> None<T>() => throw Ghost();

        [SpecOp("SortedSetCount.one")]
        internal static Seq<T> One<T>(T x) => throw Ghost();

        [SpecOp("SortedSetCount.unfound_s")]
        internal static SpecInt UnfoundS<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, Seq<T> ks, Seq<T> s) => throw Ghost();

        // The loop: `Lookup` is what it relies on of the tree it searches and the keys it
        // counts; `LoopInv` its invariant after `i` items; `Fits` that every position in the
        // tree is below `lim`.
        [SpecOp("SortedSetCount.lookup_s")]
        internal static bool Lookup<T, TTag>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, SpecTree<(T, TTag)> tr, Seq<T> ks) => throw Ghost();

        [SpecOp("SortedSetCount.loop_inv_s")]
        internal static bool LoopInv<T, TTag>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, SpecTree<(T, TTag)> tr, Seq<T> ks,
                                              Seq<bool> m, Seq<T> all, SpecInt i, SpecInt uniq, SpecInt unf) => throw Ghost();

        [SpecOp("SortedSetCount.fits")]
        internal static bool Fits<T, TTag>(IComparer<T> c, SpecTree<(T, TTag)> tr, SpecInt lim) => throw Ghost();

        // Lemmas.
        [SpecOp("SortedSetCount.red_black_height")]
        internal static void RedBlackHeight<T>(SpecTree<(T, bool)> t) => throw Ghost();

        [SpecOp("SortedSetCount.range_root_height")]
        internal static void RangeRootHeight<T, TTag>(IComparer<T> c, SpecTree<(T, TTag)> t, T lo, T hi, bool la, bool ua) => throw Ghost();

        [SpecOp("SortedSetCount.shift_one")]
        internal static void ShiftOne(SpecInt h) => throw Ghost();

        [SpecOp("SortedSetCount.fits_pow2")]
        internal static void FitsPow2<T, TTag>(IComparer<T> c, SpecTree<(T, TTag)> tr, SpecInt h) => throw Ghost();

        [SpecOp("SortedSetCount.range_depth_le_size")]
        internal static void RangeDepthLeSize<T, TTag>(IComparer<T> c, SpecTree<(T, TTag)> t, T lo, T hi, bool la, bool ua) => throw Ghost();

        // `lookup` of the tree a set (no bound active) or a view searches: the range root of
        // the set's tree, which is the whole tree when no bound is active.
        [SpecOp("SortedSetCount.lookup_intro_s")]
        internal static void LookupIntro<T, TTag>(IComparer<T> c, SpecTree<(T, TTag)> t, Seq<T> los, Seq<T> his, bool la, bool ua) => throw Ghost();

        [SpecOp("SortedSetCount.loop_start_s")]
        internal static void LoopStart<T, TTag>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, SpecTree<(T, TTag)> tr, Seq<T> ks,
                                                Seq<bool> m, Seq<T> all) => throw Ghost();

        [SpecOp("SortedSetCount.loop_step_s")]
        internal static void LoopStep<T, TTag>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, SpecTree<(T, TTag)> tr, Seq<T> ks,
                                               Seq<bool> m, Seq<T> all, SpecInt i, SpecInt uniq, SpecInt unf) => throw Ghost();

        // Used only by the experiment that checks the body before dotnet/runtime#133116
        // (samples/dotnet-runtime/SORTEDSET-PR133116.md).
        [SpecOp("SortedSetCount.loop_step_beyond_s")]
        internal static void LoopStepBeyond<T, TTag>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, SpecTree<(T, TTag)> tr, Seq<T> ks,
                                                     Seq<bool> m, Seq<T> all, SpecInt i, SpecInt uniq, SpecInt unf) => throw Ghost();

        [SpecOp("SortedSetCount.loop_done_s")]
        internal static void LoopDone<T, TTag>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, SpecTree<(T, TTag)> tr, Seq<T> ks,
                                               Seq<bool> m, Seq<T> all, SpecInt i, SpecInt uniq, SpecInt unf) => throw Ghost();

        [SpecOp("SortedSetCount.loop_end_s")]
        internal static void LoopEnd<T, TTag>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, SpecTree<(T, TTag)> tr, Seq<T> ks,
                                              Seq<bool> m, Seq<T> all, SpecInt uniq, SpecInt unf, bool stopped) => throw Ghost();

        [SpecOp("SortedSetCount.empty_counts_s")]
        internal static void EmptyCounts<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, Seq<T> ks, Seq<T> s) => throw Ghost();

        // The counts the contracts state, from the body's: the set's, or the view's range's.
        [SpecOp("SortedSetCount.counts_s")]
        internal static void Counts<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua, Seq<T> ks, Seq<T> s) => throw Ghost();

        // What the callers decide (R37.10). `AllHit(c, s, t)`: every item of `t` is equivalent
        // under `c` to an item of `s`; neither need be sorted under `c`.
        [SpecOp("SortedSetCount.all_hit")]
        internal static bool AllHit<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

        // On a strictly sorted `ks`: `FoundAll == |ks|` iff `s` holds every key, and
        // `UnfoundAll == 0` iff the keys hold every item of `s`.
        [SpecOp("SortedSetCount.counts_decide")]
        internal static void CountsDecide<T>(IComparer<T> c, Seq<T> ks, Seq<T> s) => throw Ghost();

        // On two sequences strictly sorted under `c`: `AllIn` is `AllHit`, a subset no shorter is
        // the whole, and `SameKeys` is inclusion both ways.
        [SpecOp("SortedSetCount.sorted_hits")]
        internal static void SortedHits<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();
    }

    public partial class SortedSet<T>
    {
        // R37.5. A client of the method at a view: `s.GetViewBetween(lo, hi)` followed by what
        // `view.SetEquals(other)` and its kin run for an `other` that is not a `SortedSet<T>`.
        // The call binds to the method's replica at `TreeSubSet` (R32.13). The set's version is
        // not -1, the fresh view's count version (doc/translation.md §32 Findings). The set is a
        // parameter, not `this`: a view of another object is held at that object's heaps
        // (§32), so the view's root keeps its facts between the two calls.
        [Requires("Pal.Compare(s.SpecComparer, lo, hi) <= 0 && s.SpecVersion != -1 && Pal.Contents(other).Length <= int.MaxValue")]
        [Ensures("(Result.UnfoundCount > 0) == (SortedSetCount.UnfoundRange(s.SpecComparer, lo, hi, true, true, s.SpecItems, Pal.Contents(other)) > 0)")]
        [Ensures("Pal.Implies(!returnIfUnfound || Result.UnfoundCount == 0, Result.UniqueCount == SortedSetCount.FoundRange(s.SpecComparer, lo, hi, true, true, s.SpecItems, Pal.Contents(other)))")]
        internal ElementCount ViewCounts(SortedSet<T> s, T lo, T hi, IEnumerable<T> other, bool returnIfUnfound)
        {
            SortedSet<T> view = s.GetViewBetween(lo, hi);
            return view.CheckUniqueAndUnfoundElements(other, returnIfUnfound);
        }
    }
}
