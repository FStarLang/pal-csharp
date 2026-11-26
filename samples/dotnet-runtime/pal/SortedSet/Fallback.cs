using PalLang;
using System.Diagnostics;

[assembly: IncludePulseFile("SortedSetInductive.Fallback.Reference.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Fallback.Bindings.fst")]

namespace System.Collections.Generic
{
    internal static class SortedSetFallback
    {
        [SpecOp("SortedSetInductive.Fallback.Bindings.seen")]
        internal static bool Seen<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all, SpecInt i, Seq<SortedSet<T>.Node> nodes) =>
            throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Fallback.Bindings.counts")]
        internal static bool Counts<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all, SpecInt i, SpecInt unique, SpecInt unfound) =>
            throw new InvalidOperationException();

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.start")]
        internal static void Start<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.step")]
        internal static void Step<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all, SpecInt i, SpecInt unique, SpecInt unfound) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.lookup")]
        internal static void Lookup<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all, SpecInt i, Seq<SortedSet<T>.Node> nodes,
            SortedSet<T>.Node? node, T item) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.hit")]
        internal static void Hit<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all, SpecInt i, Seq<SortedSet<T>.Node> before,
            Seq<SortedSet<T>.Node> after, SortedSet<T>.Node? node) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.miss")]
        internal static void Miss<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all, SpecInt i, Seq<SortedSet<T>.Node> nodes) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.done_")]
        internal static void Done<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all, SpecInt i, SpecInt unique, SpecInt unfound, bool stop) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.finish")]
        internal static void Finish<T>(IComparer<T> c, Seq<T> los, Seq<T> his, bool la, bool ua,
            SortedSetLabels<T> tree, Seq<T> all, SpecInt unique, SpecInt unfound, bool stopped) { }

        [SpecOp("SortedSetInductive.Fallback.Bindings.node_mem")]
        internal static bool NodeMem<T>(Seq<SortedSet<T>.Node> nodes, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.reference_mem")]
        internal static void ReferenceMem<T>(IEqualityComparer<SortedSet<T>.Node>? comparer,
            Seq<SortedSet<T>.Node> nodes, SortedSet<T>.Node? node) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.added")]
        internal static void Added<T>(Seq<SortedSet<T>.Node> before, Seq<SortedSet<T>.Node> after,
            SortedSet<T>.Node? node) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.unchanged")]
        internal static void Unchanged<T>(Seq<SortedSet<T>.Node> nodes, SortedSet<T>.Node? node) { }

        [Conditional("PAL"), SpecOp("SortedSetInductive.Fallback.Bindings.default_after")]
        internal static void DefaultAfter<T>(IEqualityComparer<SortedSet<T>.Node>? before,
            IEqualityComparer<SortedSet<T>.Node>? after) { }
    }
}
