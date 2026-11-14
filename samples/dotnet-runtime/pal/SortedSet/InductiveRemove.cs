#if PAL
using System;
using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetRemove
    {
        [SpecOp("SortedSetInductive.Remove.inv")]
        internal static bool Inv<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.mid")]
        internal static bool Mid<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found, SpecInt measure) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.fixed")]
        internal static bool Fixed<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found, SpecInt measure) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.measure")]
        internal static SpecInt Measure<T>(SortedSetLabels<T> n, SortedSet<T>.Node? cur) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.order")]
        internal static SpecInt Order<T>(IComparer<T> c, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.next")]
        internal static SortedSet<T>.Node? Next<T>(SortedSetLabels<T> n, SortedSet<T>.Node? cur, SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.sibling")]
        internal static SortedSet<T>.Node? Sibling<T>(SortedSetLabels<T> n, SortedSet<T>.Node? par, SortedSet<T>.Node? cur) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.lifted")]
        internal static SortedSetLabels<T> Lifted<T>(SortedSetLabels<T> n, SortedSet<T>.Node? par, SortedSet<T>.Node? cur) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.borrowed")]
        internal static SortedSetLabels<T> Borrowed<T>(SortedSetLabels<T> n, SortedSet<T>.Node? par, SortedSet<T>.Node? cur) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.rotation")]
        internal static TreeRotation Rotation<T>(SortedSetLabels<T> n, SortedSet<T>.Node? par, SortedSet<T>.Node? cur) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.new_parent")]
        internal static SortedSet<T>.Node? NewParent<T>(SortedSetLabels<T> n, SortedSet<T>.Node? par, SortedSet<T>.Node? cur) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDownRemove.pom_a")]
        internal static SortedSet<T>.Node? NewMatchParent<T>(SortedSet<T>.Node? par, SortedSet<T>.Node? match,
            SortedSet<T>.Node? newParent, SortedSet<T>.Node? pom) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveResult.after")]
        internal static bool After<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? par, SortedSet<T>.Node? gp, SortedSet<T>.Node? match, SortedSet<T>.Node? pom) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Remove.start")]
        internal static void Start<T>(IComparer<T> c, T key, SortedSetLabels<T> n) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.at_cur")]
        internal static void AtCur<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.not2")]
        internal static void Not2<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.root")]
        internal static void Root<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.direct")]
        internal static void Direct<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.merge")]
        internal static void Merge<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found, SpecInt measure) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.advance")]
        internal static void Advance<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found, SpecInt measure, SpecInt order) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.at_fixed")]
        internal static void AtFixed<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found, SpecInt measure) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.at_sib")]
        internal static void AtSibling<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.at_mid")]
        internal static void AtMid<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found, SpecInt measure) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.lift")]
        internal static void Lift<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.borrow")]
        internal static void Borrow<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? cur, SortedSet<T>.Node? par, SortedSet<T>.Node? gp,
            SortedSet<T>.Node? match, SortedSet<T>.Node? pom, bool found, SpecInt measure) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRepair.selection")]
        internal static void Selection<T>(SortedSetLabels<T> n, SortedSet<T>.Node? par, SortedSet<T>.Node? cur) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveResult.end_search")]
        internal static void End<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n,
            SortedSet<T>.Node? par, SortedSet<T>.Node? gp, SortedSet<T>.Node? match,
            SortedSet<T>.Node? pom, bool found) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveResult.finish")]
        internal static void Finish<T>(IComparer<T> c, Seq<T> keys, T key, SortedSetLabels<T> n) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveResult.cardinality")]
        internal static void Cardinality<T>(IComparer<T> c, Seq<T> keys, T key) => throw new InvalidOperationException();
    }

    internal static class SortedSetLift
    {
        [SpecOp("SortedSetInductive.Lift.child")]
        internal static bool Child<T>(SortedSetLabels<T> n, SortedSet<T>.Node? child) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Lift.right")]
        internal static bool Right<T>(SortedSetLabels<T> n, SortedSet<T>.Node? child) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Lift.rotated")]
        internal static SortedSetLabels<T> Rotated<T>(SortedSetLabels<T> n, SortedSet<T>.Node? child) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Lift.lifted")]
        internal static SortedSetLabels<T> Lifted<T>(SortedSetLabels<T> n, SortedSet<T>.Node? child) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Lift.layout")]
        internal static void Layout<T>(SortedSetLabels<T> n, SortedSet<T>.Node? child) => throw new InvalidOperationException();
    }
}
#endif
