#if PAL
using System;
using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetInsert
    {
        [SpecOp("SortedSetInductive.Insert.inv")]
        internal static bool Inv<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? current, SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent,
            SortedSet<T>.Node? greatGrandParent, SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.ready")]
        internal static bool Ready<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? current, SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent,
            SpecInt order, SpecInt measure) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.measure")]
        internal static SpecInt Measure<T>(IComparer<T> comparer, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? current) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.complete")]
        internal static bool Complete<T>(IComparer<T> comparer, Seq<T> keys, T item,
            SortedSet<T>.Node? root, SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.linked_result")]
        internal static bool LinkedResult<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? node, SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent,
            SortedSet<T>.Node? greatGrandParent, SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.expected")]
        internal static Seq<T> Expected<T>(IComparer<T> comparer, Seq<T> keys, T item) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.ok")]
        internal static bool Ok<T>(IComparer<T> comparer, Seq<T> keys, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.black")]
        internal static SortedSetLabels<T> Black<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();

        // These are checked pure lemmas; their F* preconditions are checked
        // at each use, just like the other library-defined specification ops.
        [SpecOp("SortedSetInductive.Insert.start")]
        internal static void Start<T>(IComparer<T> comparer, T item, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.at_cur")]
        internal static void AtCur<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? current, SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent,
            SortedSet<T>.Node? greatGrandParent, SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.look")]
        internal static void Look<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? current, SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent,
            SortedSet<T>.Node? greatGrandParent, SpecInt oldOrder, SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.split_step")]
        internal static void SplitStep<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? current, SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent,
            SortedSet<T>.Node? greatGrandParent, SpecInt oldOrder, SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.advance")]
        internal static void Advance<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? current, SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent,
            SortedSet<T>.Node? next, SpecInt order, SpecInt measure) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.at_end")]
        internal static void AtEnd<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent, SortedSet<T>.Node? greatGrandParent,
            SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.linked_leaf")]
        internal static void Linked<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels,
            SortedSet<T>.Node? node, SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent,
            SortedSet<T>.Node? greatGrandParent, SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.balance_nodes")]
        internal static void BalanceNodes<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? current,
            SortedSet<T>.Node? parent, SortedSet<T>.Node? grandParent, SortedSet<T>.Node? greatGrandParent) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.finish")]
        internal static void Finish<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.new_root")]
        internal static void NewRoot<T>(IComparer<T> comparer, Seq<T> keys, T item, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.singleton")]
        internal static void Singleton<T>(IComparer<T> comparer, T item, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.result_facts")]
        internal static void ResultFacts<T>(IComparer<T> comparer, Seq<T> keys, T item,
            SortedSet<T>.Node? root, SortedSetLabels<T> labels) => throw new InvalidOperationException();
    }
}
#endif
