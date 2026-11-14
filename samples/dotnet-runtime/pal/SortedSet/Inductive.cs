#if PAL
using System;
using System.Diagnostics;
using PalLang;
using static System.Collections.Generic.SortedSetWalk;

[assembly: IncludePulseFile("SortedSetInductive.Ownership.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Cursor.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Edit.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Mutation.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Relink.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Leaf.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Local.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Frontier.fst")]
[assembly: IncludePulseFile("SortedSetInductive.MergeFrontier.fst")]
[assembly: IncludePulseFile("SortedSetInductive.FrontierClient.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Rotation.fst")]
[assembly: IncludePulseFile("SortedSetInductive.RotationClient.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Balance.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Insert.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Successor.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Remove.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Lift.fst")]
[assembly: IncludePulseFile("SortedSetInductive.RemoveRotation.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Borrow.fst")]
[assembly: IncludePulseFile("SortedSetInductive.RemoveRepair.fst")]
[assembly: IncludePulseFile("SortedSetInductive.RemoveResult.fst")]
[assembly: IncludePulseFile("SortedSetInductive.RemoveDispatch.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Selector.fst")]
[assembly: IncludePulseFile("SortedSetInductive.RemoveDispatchClient.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Read.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Valid.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Read.Branch.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Read.BranchClient.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Read.Point.fst")]
[assembly: IncludePulseFile("SortedSetInductive.StateCorrespondence.fst")]
[assembly: IncludePulseFile("SortedSetInductive.StateCases.fst")]
[assembly: IncludePulseFile("SortedSetInductive.RetainedHolder.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Walk.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Breadth.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Range.fst")]
[assembly: IncludePulseFile("SortedSetInductive.RangeBreadth.fst")]

namespace System.Collections.Generic
{
    [SpecType("SortedSetInductive.Ownership.tree")]
    internal readonly struct SortedSetLabels<T> { }

    [SpecType("SortedSetInductive.Ownership.state")]
    internal readonly struct SortedSetOwnershipState<T> { }

    [SpecType("Class_SortedSet.class_SortedSet__model")]
    internal readonly struct SortedSetSnapshot<T> { }

    [SpecType("SortedSetInductive.Read.handle")]
    internal readonly struct SortedSetReadHandle<T> { }

    [SpecType("Class_Node.class_Node__raw")]
    internal readonly struct SortedSetNodeSnapshot<T> { }

    [SpecType("SortedSetInductive.Ownership.nullable_snapshot")]
    internal readonly struct SortedSetNullableSnapshot<T> { }

    internal static class SortedSetOwnership
    {
        [SpecOp("SortedSetInductive.Valid.state")]
        internal static bool Valid<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state,
            IComparer<T> comparer, SpecInt count, SpecInt version) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Read.snapshot_of")]
        internal static SortedSetSnapshot<T> Snapshot<T>(SortedSetModel<T> model) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Read.handle_of_view")]
        internal static SortedSetReadHandle<T> ViewHandle<T>(SortedSet<T>.TreeSubSet view, SortedSetSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.handle_of_view_facts")]
        internal static void ViewHandleFacts<T>(SortedSet<T>.TreeSubSet view, SortedSetSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.handle_matches_view")]
        internal static bool HandleMatchesView<T>(SortedSetReadHandle<T> handle, SortedSet<T>.TreeSubSet view, SortedSetSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.handle_matches")]
        internal static bool HandleMatches<T>(SortedSetReadHandle<T> handle, SortedSet<T> owner, SortedSetSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.set_window")]
        internal static SlProp SetWindow<T>(SortedSet<T> owner, SortedSetSnapshot<T> snapshot,
            SortedSetLabels<T> tree, SortedSet<T>.Node? node, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.Point.point")]
        internal static SlProp SetPoint<T>(SortedSet<T> owner, SortedSetSnapshot<T> snapshot,
            SortedSetLabels<T> tree, SortedSet<T>.Node? node, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.Point.tree_point")]
        internal static SlProp TreePoint<T>(SortedSetLabels<T> tree, SortedSet<T>.Node? node, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.Point.any_tree_point")]
        internal static SlProp AnyTreePoint<T>(SortedSetLabels<T> tree, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.Branch.handle_or_closed")]
        internal static SlProp HandleOrClosed<T>([Plain] SortedSet<T> owner, SortedSetSnapshot<T> snapshot,
            SortedSetReadHandle<T> handle, SortedSetLabels<T> tree, SortedSet<T>.Node? node,
            Perm permission, bool returned) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Read.handle_window")]
        internal static SlProp HandleWindow<T>(SortedSetReadHandle<T> handle, SortedSetLabels<T> tree,
            SortedSet<T>.Node? node, Perm permission) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.empty")]
        internal static SortedSetOwnershipState<T> Empty<T>() => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.cleared")]
        internal static SortedSetOwnershipState<T> Cleared<T>(SortedSetOwnershipState<T> state) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.retired_cell")]
        internal static SortedSetOwnershipState<T> RetiredCell<T>(SortedSetOwnershipState<T> state,
            SortedSet<T>.Node? node, Ghost<SortedSetNodeSnapshot<T>> snapshot) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.fresh")]
        internal static SlProp Fresh<T>(SortedSet<T>.Node node, T item, NodeColor color) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.recolor")]
        internal static SortedSetNodeSnapshot<T> Recolor<T>(SortedSetNodeSnapshot<T> snapshot, bool red) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.owner")]
        internal static SlProp Owner<T>(SortedSet<T>.Node? root,
            SortedSetOwnershipState<T> state, Perm permission) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.active")]
        internal static SortedSetLabels<T> Active<T>(SortedSetOwnershipState<T> state) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.values")]
        internal static SpecTree<(T, bool)> Values<T>(SortedSetLabels<T> tree) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.top")]
        internal static SortedSet<T>.Node? Top<T>(SortedSetLabels<T> tree) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.good")]
        internal static bool Good<T>(SortedSetLabels<T> tree) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.member")]
        internal static bool Member<T>(SortedSetLabels<T> tree, SortedSet<T>.Node? node) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.lookup")]
        internal static SpecTree<(T, bool)> Lookup<T>(SortedSetLabels<T> tree, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.raw")]
        internal static SlProp Raw<T>(SortedSet<T>.Node? node, SortedSetNodeSnapshot<T> snapshot,
            Perm permission) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.item")]
        internal static T Item<T>(SortedSetNodeSnapshot<T> snapshot) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.red")]
        internal static bool Red<T>(SortedSetNodeSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.entry")]
        internal static (T, bool) Entry<T>(SortedSetNodeSnapshot<T> snapshot) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.node_color")]
        internal static NodeColor Color<T>(SortedSetNodeSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.left")]
        internal static SortedSet<T>.Node? Left<T>(SortedSetNodeSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.right")]
        internal static SortedSet<T>.Node? Right<T>(SortedSetNodeSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.with_left")]
        internal static SortedSetNodeSnapshot<T> WithLeft<T>(SortedSetNodeSnapshot<T> snapshot, SortedSet<T>.Node? node) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.with_right")]
        internal static SortedSetNodeSnapshot<T> WithRight<T>(SortedSetNodeSnapshot<T> snapshot, SortedSet<T>.Node? node) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.with_children")]
        internal static SortedSetNodeSnapshot<T> WithChildren<T>(SortedSetNodeSnapshot<T> snapshot, SortedSet<T>.Node? left, SortedSet<T>.Node? right) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.nullable_raw")]
        internal static SlProp NullableRaw<T>(SortedSet<T>.Node? node, SortedSetNullableSnapshot<T> snapshot, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.nullable_red")]
        internal static bool NullableRed<T>(SortedSetNullableSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Ownership.nullable_opened")]
        internal static SlProp NullableOpened<T>(SortedSet<T>.Node node, SortedSetNullableSnapshot<T> snapshot, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Cursor.owner_window")]
        internal static SlProp Window<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state,
            SortedSet<T>.Node? node, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Cursor.any_owner_window")]
        internal static SlProp AnyWindow<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state,
            Perm permission) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Ownership.owns")]
        internal static SlProp Owns<T>(SortedSetLabels<T> tree, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Cursor.window")]
        internal static SlProp TreeWindow<T>(SortedSetLabels<T> tree, SortedSet<T>.Node? node, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.any_window")]
        internal static SlProp AnyTreeWindow<T>(SortedSetLabels<T> tree, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.inv")]
        internal static SlProp SetInv<T>(SortedSet<T> set, SortedSetSnapshot<T> snapshot, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.labels")]
        internal static SortedSetLabels<T> SnapshotLabels<T>(SortedSetSnapshot<T> snapshot) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.owner_lease")]
        internal static SlProp OwnerLease<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state,
            SortedSetLabels<T> tree, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.set_lease")]
        internal static SlProp SetLease<T>(SortedSet<T> set, SortedSetSnapshot<T> snapshot,
            SortedSetLabels<T> tree, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Read.view_root")]
        internal static bool ViewRoot<T>(SortedSetLabels<T> tree, IComparer<T> comparer,
            SortedSet<T>.Node? root, SpecInt level, T lower, T upper, bool lowerActive, bool upperActive) => throw new InvalidOperationException();
    }

    internal static class SortedSetWalk
    {
        [SpecOp("SortedSetInductive.Walk.pending")]
        internal static Seq<T> Pending<T>(bool reverse, SortedSetLabels<T> tree,
            Seq<SortedSet<T>.Node?> stack) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Walk.walkable")]
        internal static bool Walkable<T>(SortedSetLabels<T> tree,
            Seq<SortedSet<T>.Node?> stack) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Walk.near_node")]
        internal static SortedSet<T>.Node? Near<T>(bool reverse, SortedSetLabels<T> tree,
            SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Walk.far_node")]
        internal static SortedSet<T>.Node? Far<T>(bool reverse, SortedSetLabels<T> tree,
            SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Walk.entry_value")]
        internal static (T, bool) Entry<T>(SortedSetLabels<T> tree,
            SortedSet<T>.Node? node) => throw new InvalidOperationException();
    }

    internal static class SortedSetBreadth
    {
        [SpecOp("SortedSetInductive.Breadth.pending")]
        internal static Seq<T> Pending<T>(SortedSetLabels<T> tree,
            Seq<SortedSet<T>.Node?> queue) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Breadth.next")]
        internal static Seq<SortedSet<T>.Node?> Next<T>(SortedSetLabels<T> tree,
            Seq<SortedSet<T>.Node?> queue) => throw new InvalidOperationException();
    }

    internal static class SortedSetBreadthProof
    {
        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Breadth.start $(tree) $(root) $(queue) $(items) $(trace)")]
        [Requires("SortedSetOwnership.Good(tree) && root == SortedSetOwnership.Top(tree) && root != null")]
        [Requires("queue == Pal.Snoc(Pal.EmptySeq<SortedSet<T>.Node?>(), root)")]
        [Requires("items == SpecSearchTree.Keys(SortedSetOwnership.Values(tree)) && trace.Length == 0")]
        [Ensures("SortedSetWalk.Walkable(tree, queue) && SpecWalk.BfVisited(items, trace, SortedSetBreadth.Pending(tree, queue))")]
        internal static void Start<T>(Ghost<SortedSetLabels<T>> tree, Ghost<SortedSet<T>.Node?> root,
            Ghost<Seq<SortedSet<T>.Node?>> queue, Ghost<Seq<T>> items, Ghost<Seq<((T, bool), bool)>> trace) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Breadth.dequeue $(tree) $(queue) $(items) $(trace)")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetWalk.Walkable(tree, queue) && queue.Length > 0")]
        [Requires("SpecWalk.BfVisited(items, trace, SortedSetBreadth.Pending(tree, queue))")]
        [Ensures("SortedSetOwnership.Member(tree, queue[0]) && queue[0] != null && trace.Length < items.Length")]
        [Ensures("queue.Length - 1 + (SortedSetWalk.Near(false, tree, queue[0]) == null ? 0 : 1) + (SortedSetWalk.Far(false, tree, queue[0]) == null ? 0 : 1) <= items.Length - trace.Length - 1")]
        [Ensures("queue.Length - 1 + SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, SortedSetWalk.Near(false, tree, queue[0]))).Length + SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, SortedSetWalk.Far(false, tree, queue[0]))).Length < items.Length - trace.Length")]
        [Ensures("SortedSetWalk.Walkable(tree, SortedSetBreadth.Next(tree, queue))")]
        [Ensures("SpecWalk.BfVisited(items, Pal.Snoc(trace, (SortedSetWalk.Entry(tree, queue[0]), true)), SortedSetBreadth.Pending(tree, SortedSetBreadth.Next(tree, queue)))")]
        [Ensures("SpecWalk.BfWalked(items, Pal.Snoc(trace, (SortedSetWalk.Entry(tree, queue[0]), false)), false)")]
        internal static void Dequeue<T>(Ghost<SortedSetLabels<T>> tree, Ghost<Seq<SortedSet<T>.Node?>> queue,
            Ghost<Seq<T>> items, Ghost<Seq<((T, bool), bool)>> trace) { }
    }

    internal static class SortedSetRangeBreadth
    {
        [SpecOp("SortedSetInductive.RangeBreadth.queue")]
        internal static bool Queue<T>(SortedSetLabels<T> tree, IComparer<T> comparer,
            Seq<SortedSet<T>.Node?> queue) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.RangeBreadth.next")]
        internal static Seq<SortedSet<T>.Node?> Next<T>(SortedSetLabels<T> tree, IComparer<T> comparer,
            T lower, T upper, bool lowerActive, bool upperActive,
            Seq<SortedSet<T>.Node?> queue) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.RangeBreadth.take_left")]
        internal static bool TakeLeft<T>(SortedSetLabels<T> tree, IComparer<T> comparer,
            T lower, bool lowerActive, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.RangeBreadth.take_right")]
        internal static bool TakeRight<T>(SortedSetLabels<T> tree, IComparer<T> comparer,
            T lower, T upper, bool upperActive, SortedSet<T>.Node? node) => throw new InvalidOperationException();
    }

    internal static class SortedSetRangeBreadthProof
    {
        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.RangeBreadth.start $(tree) $(comparer) $(lower) $(upper) $(lowerActive) $(upperActive) $(root) $(queue) $(items) $(trace)")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetOwnership.Member(tree, root)")]
        [Requires("Pal.Same(queue, Pal.Snoc(Pal.EmptySeq<SortedSet<T>.Node?>(), root)) && trace.Length == 0")]
        [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, root)))")]
        [Requires("Pal.Same(SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, root))), items)")]
        [Ensures("SortedSetRangeBreadth.Queue(tree, comparer, queue) && SortedSetWalk.Walkable(tree, queue)")]
        [Ensures("SortedSetBreadth.Pending(tree, queue).Length == SortedSetOwnership.Lookup(tree, root).Size")]
        [Ensures("SpecWalk.BfVisited(items, trace, SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, SortedSetBreadth.Pending(tree, queue)))")]
        internal static void Start<T>(Ghost<SortedSetLabels<T>> tree, IComparer<T> comparer,
            T lower, T upper, bool lowerActive, bool upperActive, Ghost<SortedSet<T>.Node?> root,
            Ghost<Seq<SortedSet<T>.Node?>> queue, Ghost<Seq<T>> items, Ghost<Seq<((T, bool), bool)>> trace) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.RangeBreadth.dequeue $(tree) $(comparer) $(lower) $(upper) $(lowerActive) $(upperActive) $(queue) $(items) $(trace)")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetRangeBreadth.Queue(tree, comparer, queue) && queue.Length > 0")]
        [Requires("SpecWalk.BfVisited(items, trace, SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, SortedSetBreadth.Pending(tree, queue)))")]
        [Ensures("SortedSetOwnership.Member(tree, queue[0]) && queue[0] != null")]
        [Ensures("SortedSetRangeBreadth.Queue(tree, comparer, Pal.Slice(queue, 1, queue.Length)) && SortedSetWalk.Walkable(tree, Pal.Slice(queue, 1, queue.Length))")]
        [Ensures("SortedSetBreadth.Pending(tree, Pal.Slice(queue, 1, queue.Length)).Length < SortedSetBreadth.Pending(tree, queue).Length")]
        [Ensures("SortedSetRangeBreadth.Queue(tree, comparer, SortedSetRangeBreadth.Next(tree, comparer, lower, upper, lowerActive, upperActive, queue)) && SortedSetWalk.Walkable(tree, SortedSetRangeBreadth.Next(tree, comparer, lower, upper, lowerActive, upperActive, queue))")]
        [Ensures("SortedSetRangeBreadth.Next(tree, comparer, lower, upper, lowerActive, upperActive, queue).Length <= SortedSetBreadth.Pending(tree, SortedSetRangeBreadth.Next(tree, comparer, lower, upper, lowerActive, upperActive, queue)).Length")]
        [Ensures("SortedSetBreadth.Pending(tree, SortedSetRangeBreadth.Next(tree, comparer, lower, upper, lowerActive, upperActive, queue)).Length < SortedSetBreadth.Pending(tree, queue).Length")]
        [Ensures("Pal.Implies(SpecSearchTree.InRange(comparer, lower, upper, lowerActive, upperActive, SortedSetWalk.Entry(tree, queue[0]).Item1), trace.Length < items.Length)")]
        [Ensures("Pal.Implies(SpecSearchTree.InRange(comparer, lower, upper, lowerActive, upperActive, SortedSetWalk.Entry(tree, queue[0]).Item1), SpecWalk.BfVisited(items, Pal.Snoc(trace, (SortedSetWalk.Entry(tree, queue[0]), true)), SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, SortedSetBreadth.Pending(tree, SortedSetRangeBreadth.Next(tree, comparer, lower, upper, lowerActive, upperActive, queue)))))")]
        [Ensures("Pal.Implies(SpecSearchTree.InRange(comparer, lower, upper, lowerActive, upperActive, SortedSetWalk.Entry(tree, queue[0]).Item1), SpecWalk.BfWalked(items, Pal.Snoc(trace, (SortedSetWalk.Entry(tree, queue[0]), false)), false))")]
        [Ensures("Pal.Implies(!SpecSearchTree.InRange(comparer, lower, upper, lowerActive, upperActive, SortedSetWalk.Entry(tree, queue[0]).Item1), SpecWalk.BfVisited(items, trace, SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, SortedSetBreadth.Pending(tree, SortedSetRangeBreadth.Next(tree, comparer, lower, upper, lowerActive, upperActive, queue)))))")]
        internal static void Dequeue<T>(Ghost<SortedSetLabels<T>> tree, IComparer<T> comparer,
            T lower, T upper, bool lowerActive, bool upperActive, Ghost<Seq<SortedSet<T>.Node?>> queue,
            Ghost<Seq<T>> items, Ghost<Seq<((T, bool), bool)>> trace) { }
    }

    internal static class SortedSetWalkProof
    {
        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Walk.empty $(reverse) $(tree) $(stack)")]
        [Requires("stack.Length == 0")]
        [Ensures("Pending(reverse, tree, stack) == Pal.EmptySeq<T>() && Walkable(tree, stack)")]
        internal static void Empty<T>(Ghost<bool> reverse, Ghost<SortedSetLabels<T>> tree,
            Ghost<Seq<SortedSet<T>.Node?>> stack) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Walk.descend $(reverse) $(tree) $(stack) $(node)")]
        [Requires("SortedSetOwnership.Good(tree) && Walkable(tree, stack) && SortedSetOwnership.Member(tree, node)")]
        [Ensures("Pal.Implies(Near(reverse, tree, node) != null, SortedSetOwnership.Member(tree, Near(reverse, tree, node)))")]
        [Ensures("Walkable(tree, Pal.Snoc(stack, node))")]
        [Ensures("stack.Length < Pal.Concat(SpecWalk.Keys(reverse, SortedSetOwnership.Lookup(tree, node)), Pending(reverse, tree, stack)).Length")]
        [Ensures("SortedSetOwnership.Lookup(tree, Near(reverse, tree, node)).Size < SortedSetOwnership.Lookup(tree, node).Size")]
        [Ensures("Pal.Concat(SpecWalk.Keys(reverse, SortedSetOwnership.Lookup(tree, node)), Pending(reverse, tree, stack)) == Pal.Concat(SpecWalk.Keys(reverse, SortedSetOwnership.Lookup(tree, Near(reverse, tree, node))), Pending(reverse, tree, Pal.Snoc(stack, node)))")]
        internal static void Descend<T>(Ghost<bool> reverse, Ghost<SortedSetLabels<T>> tree,
            Ghost<Seq<SortedSet<T>.Node?>> stack, Ghost<SortedSet<T>.Node?> node) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Walk.pop_at $(reverse) $(tree) $(stack) $(items) $(index)")]
        [Requires("SortedSetOwnership.Good(tree) && Walkable(tree, stack) && stack.Length > 0 && 0 <= index && index <= items.Length")]
        [Requires("Pending(reverse, tree, stack) == Pal.Slice(items, index, items.Length)")]
        [Ensures("SortedSetOwnership.Member(tree, stack[stack.Length - 1]) && stack[stack.Length - 1] != null && index < items.Length")]
        [Ensures("Walkable(tree, Pal.Slice(stack, 0, stack.Length - 1))")]
        [Ensures("Pal.Implies(Far(reverse, tree, stack[stack.Length - 1]) != null, SortedSetOwnership.Member(tree, Far(reverse, tree, stack[stack.Length - 1])))")]
        [Ensures("SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, stack[stack.Length - 1]).RootOnly) == Pal.Snoc(Pal.EmptySeq<T>(), items[index])")]
        [Ensures("Pal.Same(SpecSearchTree.RootKey(SortedSetOwnership.Lookup(tree, stack[stack.Length - 1]), items[index]), items[index])")]
        [Ensures("Pal.Concat(SpecWalk.Keys(reverse, SortedSetOwnership.Lookup(tree, Far(reverse, tree, stack[stack.Length - 1]))), Pending(reverse, tree, Pal.Slice(stack, 0, stack.Length - 1))) == Pal.Slice(items, index + 1, items.Length)")]
        internal static void PopAt<T>(Ghost<bool> reverse, Ghost<SortedSetLabels<T>> tree,
            Ghost<Seq<SortedSet<T>.Node?>> stack, Ghost<Seq<T>> items, Ghost<SpecInt> index) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Walk.trace_step $(items) $(before) $(after) $(result)")]
        [Requires("SpecWalk.Visited(items, before) && before.Length < items.Length && after.Length == before.Length + 1")]
        [Requires("Pal.Slice(after, 0, before.Length) == before")]
        [Requires("Pal.Same(after[before.Length].Item1.Item1, items[before.Length]) && after[before.Length].Item2 == result")]
        [Ensures("result ? SpecWalk.Visited(items, after) : SpecWalk.Walked(items, after, false)")]
        internal static void TraceStep<T>(Ghost<Seq<T>> items, Ghost<Seq<((T, bool), bool)>> before,
            Ghost<Seq<((T, bool), bool)>> after, Ghost<bool> result) { }
    }

    internal static class SortedSetRange
    {
        [SpecOp("SortedSetInductive.Range.walkable")]
        internal static bool Walkable<T>(SortedSetLabels<T> tree, IComparer<T> comparer, T lower, T upper,
            bool lowerActive, bool upperActive, Seq<SortedSet<T>.Node?> stack) => throw new InvalidOperationException();
    }

    internal static class SortedSetRangeProof
    {
        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Range.start $(tree) $(comparer) $(lower) $(upper) $(lowerActive) $(upperActive) $(node) $(stack) $(keys)")]
        [Requires("stack.Length == 0")]
        [Requires("Pal.Same(SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, node))), keys)")]
        [Ensures("Pal.Same(SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, node)), SortedSetWalk.Pending(false, tree, stack))), keys)")]
        internal static void Start<T>(Ghost<SortedSetLabels<T>> tree, IComparer<T> comparer, T lower, T upper,
            bool lowerActive, bool upperActive, Ghost<SortedSet<T>.Node?> node,
            Ghost<Seq<SortedSet<T>.Node?>> stack, Ghost<Seq<T>> keys) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Range.empty $(tree) $(comparer) $(lower) $(upper) $(lowerActive) $(upperActive) $(stack)")]
        [Requires("stack.Length == 0")]
        [Ensures("SortedSetRange.Walkable(tree, comparer, lower, upper, lowerActive, upperActive, stack) && SortedSetWalk.Walkable(tree, stack) && SortedSetWalk.Pending(false, tree, stack) == Pal.EmptySeq<T>()")]
        internal static void Empty<T>(Ghost<SortedSetLabels<T>> tree, IComparer<T> comparer, T lower, T upper,
            bool lowerActive, bool upperActive, Ghost<Seq<SortedSet<T>.Node?>> stack) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Range.push $(tree) $(comparer) $(lower) $(upper) $(lowerActive) $(upperActive) $(stack) $(node)")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetRange.Walkable(tree, comparer, lower, upper, lowerActive, upperActive, stack) && SortedSetOwnership.Member(tree, node)")]
        [Requires("SpecSearchTree.InRange(comparer, lower, upper, lowerActive, upperActive, SpecSearchTree.RootKey(SortedSetOwnership.Lookup(tree, node), lower)) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, node)))")]
        [Ensures("SortedSetRange.Walkable(tree, comparer, lower, upper, lowerActive, upperActive, Pal.Snoc(stack, node))")]
        [Ensures("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, SortedSetWalk.Near(false, tree, node))))")]
        internal static void Push<T>(Ghost<SortedSetLabels<T>> tree, IComparer<T> comparer, T lower, T upper,
            bool lowerActive, bool upperActive, Ghost<Seq<SortedSet<T>.Node?>> stack, SortedSet<T>.Node? node) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Range.skip_right $(tree) $(comparer) $(lower) $(upper) $(lowerActive) $(upperActive) $(node) $(rest)")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetOwnership.Member(tree, node) && lowerActive && Pal.Compare(comparer, lower, SpecSearchTree.RootKey(SortedSetOwnership.Lookup(tree, node), lower)) > 0 && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, node)))")]
        [Ensures("Pal.Implies(SortedSetWalk.Far(false, tree, node) != null, SortedSetOwnership.Member(tree, SortedSetWalk.Far(false, tree, node)))")]
        [Ensures("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, SortedSetWalk.Far(false, tree, node)))) && SortedSetOwnership.Lookup(tree, SortedSetWalk.Far(false, tree, node)).Size < SortedSetOwnership.Lookup(tree, node).Size")]
        [Ensures("SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, node)), rest)) == SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, SortedSetWalk.Far(false, tree, node))), rest))")]
        internal static void SkipRight<T>(Ghost<SortedSetLabels<T>> tree, IComparer<T> comparer, T lower, T upper,
            bool lowerActive, bool upperActive, SortedSet<T>.Node? node, Ghost<Seq<T>> rest) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Range.skip_left $(tree) $(comparer) $(lower) $(upper) $(lowerActive) $(upperActive) $(node) $(rest)")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetOwnership.Member(tree, node) && !SpecSearchTree.InRange(comparer, lower, upper, lowerActive, upperActive, SpecSearchTree.RootKey(SortedSetOwnership.Lookup(tree, node), lower)) && !(lowerActive && Pal.Compare(comparer, lower, SpecSearchTree.RootKey(SortedSetOwnership.Lookup(tree, node), lower)) > 0) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, node)))")]
        [Ensures("Pal.Implies(SortedSetWalk.Near(false, tree, node) != null, SortedSetOwnership.Member(tree, SortedSetWalk.Near(false, tree, node)))")]
        [Ensures("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, SortedSetWalk.Near(false, tree, node)))) && SortedSetOwnership.Lookup(tree, SortedSetWalk.Near(false, tree, node)).Size < SortedSetOwnership.Lookup(tree, node).Size")]
        [Ensures("SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, node)), rest)) == SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, SortedSetWalk.Near(false, tree, node))), rest))")]
        internal static void SkipLeft<T>(Ghost<SortedSetLabels<T>> tree, IComparer<T> comparer, T lower, T upper,
            bool lowerActive, bool upperActive, SortedSet<T>.Node? node, Ghost<Seq<T>> rest) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Range.pop_at $(tree) $(comparer) $(lower) $(upper) $(lowerActive) $(upperActive) $(stack) $(items) $(index)")]
        [Requires("SortedSetOwnership.Good(tree) && stack.Length > 0 && SortedSetWalk.Walkable(tree, stack) && SortedSetRange.Walkable(tree, comparer, lower, upper, lowerActive, upperActive, stack) && 0 <= index && index <= items.Length")]
        [Requires("SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, SortedSetWalk.Pending(false, tree, stack)) == Pal.Slice(items, index, items.Length)")]
        [Ensures("SortedSetOwnership.Member(tree, stack[stack.Length - 1]) && stack[stack.Length - 1] != null && index < items.Length")]
        [Ensures("SortedSetWalk.Walkable(tree, Pal.Slice(stack, 0, stack.Length - 1)) && SortedSetRange.Walkable(tree, comparer, lower, upper, lowerActive, upperActive, Pal.Slice(stack, 0, stack.Length - 1))")]
        [Ensures("Pal.Implies(SortedSetWalk.Far(false, tree, stack[stack.Length - 1]) != null, SortedSetOwnership.Member(tree, SortedSetWalk.Far(false, tree, stack[stack.Length - 1])))")]
        [Ensures("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(tree, SortedSetWalk.Far(false, tree, stack[stack.Length - 1])))) && Pal.Same(SpecSearchTree.RootKey(SortedSetOwnership.Lookup(tree, stack[stack.Length - 1]), lower), items[index])")]
        [Ensures("SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, SortedSetWalk.Far(false, tree, stack[stack.Length - 1]))).Length + SortedSetWalk.Pending(false, tree, Pal.Slice(stack, 0, stack.Length - 1)).Length < SortedSetWalk.Pending(false, tree, stack).Length")]
        [Ensures("SpecRangeWalk.Filter(comparer, lower, upper, lowerActive, upperActive, Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(tree, SortedSetWalk.Far(false, tree, stack[stack.Length - 1]))), SortedSetWalk.Pending(false, tree, Pal.Slice(stack, 0, stack.Length - 1)))) == Pal.Slice(items, index + 1, items.Length)")]
        internal static void PopAt<T>(Ghost<SortedSetLabels<T>> tree, IComparer<T> comparer, T lower, T upper,
            bool lowerActive, bool upperActive, Ghost<Seq<SortedSet<T>.Node?>> stack, Ghost<Seq<T>> items,
            Ghost<SpecInt> index) { }
    }

    internal static class SortedSetOwnershipProof
    {
        [Lemma, Conditional("PAL")]
        [Requires("SpecSearchTree.IndexRoom(index, tree, height) && height <= 30 && !tree.IsLeaf")]
        [Ensures("0 <= index && 2 * (SpecInt)index + 2 <= 2147483646")]
        [PulseBody("Pulse.Lib.CSharp.SearchTree.index_room_int (FStar.Int32.v $(index)) $(tree) $(height)")]
        internal static void IndexBounds<T>(int index, Ghost<SpecTree<(T, bool)>> tree, Ghost<SpecInt> height) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Read.begin_owner $(root) $(state) $(tree) $(permission)")]
        [Requires("SortedSetOwnership.Owner(root, state, permission)")]
        [Requires("Pal.Same(tree, SortedSetOwnership.Active(state))")]
        [Ensures("SortedSetOwnership.OwnerLease(root, state, tree, permission)")]
        internal static void ReadOwner<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state,
            Ghost<SortedSetLabels<T>> tree, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [GhostArg("SortedSet<T> owner"), GhostArg("SortedSetSnapshot<T> snapshot")]
        [PulseBody("SortedSetInductive.Read.begin_set $(owner) $(snapshot) $(tree) $(permission)")]
        [Requires("SortedSetOwnership.SetInv(owner, snapshot, permission)")]
        [Requires("Pal.Same(tree, SortedSetOwnership.SnapshotLabels(snapshot))")]
        [Ensures("SortedSetOwnership.SetLease(owner, snapshot, tree, permission)")]
        internal static void ReadSet<T>(Ghost<SortedSetLabels<T>> tree, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [GhostArg("SortedSet<T> owner"), GhostArg("SortedSetSnapshot<T> snapshot")]
        [PulseBody("SortedSetInductive.Read.Point.open_set $(owner) $(snapshot) $(tree) $(node) $(permission)")]
        [Requires("SortedSetOwnership.SetInv(owner, snapshot, permission)")]
        [Requires("Pal.Same(tree, SortedSetOwnership.SnapshotLabels(snapshot))")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetOwnership.Member(tree, node)")]
        [Ensures("SortedSetOwnership.SetPoint(owner, snapshot, tree, node, permission)")]
        internal static void ReadSetAt<T>(Ghost<SortedSetLabels<T>> tree, SortedSet<T>.Node? node,
            Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [GhostArg("SortedSet<T> owner"), GhostArg("SortedSetSnapshot<T> snapshot")]
        [PulseBody("SortedSetInductive.Read.Point.close_return $(owner) $(snapshot) $(permission)")]
        [Requires("SortedSetOwnership.SetPoint(owner, snapshot, tree, node, permission)")]
        [Ensures("SortedSetOwnership.SetInv(owner, snapshot, permission)")]
        internal static void CloseSetPoint<T>(Ghost<SortedSetLabels<T>> tree, SortedSet<T>.Node? node,
            Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [Requires("SortedSetOwnership.Owns(tree, permission)")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetOwnership.Member(tree, node)")]
        [Ensures("SortedSetOwnership.TreePoint(tree, node, permission)")]
        [PulseBody("SortedSetInductive.Read.Point.open_tree $(tree) $(node) $(permission)")]
        internal static void OpenTreePoint<T>(Ghost<SortedSetLabels<T>> tree, SortedSet<T>.Node? node,
            Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [Requires("SortedSetOwnership.AnyTreePoint(tree, permission)")]
        [Ensures("SortedSetOwnership.Owns(tree, permission)")]
        [PulseBody("SortedSetInductive.Read.Point.close_tree $(tree) $(permission)")]
        internal static void CloseTreePoint<T>(Ghost<SortedSetLabels<T>> tree, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [GhostArg("SortedSet<T> owner"), GhostArg("SortedSetSnapshot<T> snapshot")]
        [PulseBody("SortedSetInductive.Read.end_set $(owner) $(snapshot) $(permission)")]
        [Requires("SortedSetOwnership.SetLease(owner, snapshot, tree, permission)")]
        [Ensures("SortedSetOwnership.SetInv(owner, snapshot, permission)")]
        internal static void EndSet<T>(Ghost<SortedSetLabels<T>> tree, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [GhostArg("SortedSet<T> owner"), GhostArg("SortedSetSnapshot<T> snapshot")]
        [PulseBody("SortedSetInductive.Read.window_to_handle $(owner) $(snapshot) $(handle) $(tree) $(node) $(permission)")]
        [Requires("SortedSetOwnership.SetWindow(owner, snapshot, tree, node, permission)")]
        [Requires("SortedSetOwnership.HandleMatches(handle, owner, snapshot)")]
        [Ensures("SortedSetOwnership.HandleWindow(handle, tree, node, permission)")]
        internal static void WindowToHandle<T>(Ghost<SortedSetReadHandle<T>> handle,
            Ghost<SortedSetLabels<T>> tree, SortedSet<T>.Node? node, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Read.window_from_handle $(owner) $(snapshot) $(handle) $(tree) $(node) $(permission)")]
        [Requires("SortedSetOwnership.HandleWindow(handle, tree, node, permission)")]
        [Requires("SortedSetOwnership.HandleMatches(handle, owner, snapshot)")]
        [Ensures("SortedSetOwnership.SetWindow(owner, snapshot, tree, node, permission)")]
        internal static void WindowFromHandle<T>([Plain] SortedSet<T> owner,
            Ghost<SortedSetSnapshot<T>> snapshot, Ghost<SortedSetReadHandle<T>> handle,
            Ghost<SortedSetLabels<T>> tree, SortedSet<T>.Node? node, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Read.Branch.continuing_handle_window $(owner) $(snapshot) $(handle) $(tree) $(node) $(permission) $(returned)")]
        [Requires("SortedSetOwnership.HandleOrClosed(owner, snapshot, handle, tree, node, permission, returned)")]
        [Requires("!returned")]
        [Ensures("SortedSetOwnership.HandleWindow(handle, tree, node, permission)")]
        internal static void ContinueHandle<T>([Plain] SortedSet<T> owner,
            Ghost<SortedSetSnapshot<T>> snapshot, Ghost<SortedSetReadHandle<T>> handle,
            Ghost<SortedSetLabels<T>> tree, SortedSet<T>.Node? node, Ghost<Perm> permission, Ghost<bool> returned) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Cursor.open_node $(tree) $(node) $(permission)")]
        [Requires("SortedSetOwnership.Owns(tree, permission)")]
        [Requires("SortedSetOwnership.Good(tree) && SortedSetOwnership.Member(tree, node)")]
        [Ensures("SortedSetOwnership.TreeWindow(tree, node, permission)")]
        internal static void OpenRead<T>(Ghost<SortedSetLabels<T>> tree, SortedSet<T>.Node? node,
            Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Read.close_window $(tree) $(permission)")]
        [Requires("SortedSetOwnership.AnyTreeWindow(tree, permission)")]
        [Ensures("SortedSetOwnership.Owns(tree, permission)")]
        internal static void CloseRead<T>(Ghost<SortedSetLabels<T>> tree, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Cursor.lookup_root $(tree)")]
        [Requires("SortedSetOwnership.Good(tree)")]
        [Ensures("SortedSetOwnership.Lookup(tree, SortedSetOwnership.Top(tree)) == SortedSetOwnership.Values(tree)")]
        [Ensures("Pal.Implies(SortedSetOwnership.Top(tree) != null, SortedSetOwnership.Member(tree, SortedSetOwnership.Top(tree)))")]
        [Ensures("SortedSetOwnership.Lookup(tree, null).IsLeaf")]
        internal static void RootFacts<T>(Ghost<SortedSetLabels<T>> tree) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Cursor.open_owner $(root) $(state) $(node) $(permission)")]
        [Requires("SortedSetOwnership.Owner(root, state, permission)")]
        [Requires("SortedSetOwnership.Good(SortedSetOwnership.Active(state)) && SortedSetOwnership.Member(SortedSetOwnership.Active(state), node)")]
        [Ensures("SortedSetOwnership.Window(root, state, node, permission)")]
        internal static void OpenNode<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state,
            SortedSet<T>.Node? node, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Cursor.close_any_owner $(root) $(state) $(permission)")]
        [Requires("SortedSetOwnership.AnyWindow(root, state, permission)")]
        [Ensures("SortedSetOwnership.Owner(root, state, permission)")]
        internal static void CloseNode<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state,
            Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Ownership.open_nullable $(node) $(snapshot) $(permission)")]
        [Requires("SortedSetOwnership.NullableRaw(node, snapshot, permission)")]
        [Ensures("SortedSetOwnership.NullableOpened(node, snapshot, permission)")]
        internal static void OpenNullable<T>(SortedSet<T>.Node node, Ghost<SortedSetNullableSnapshot<T>> snapshot, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Ownership.close_nullable $(node) $(snapshot) $(permission)")]
        [Requires("SortedSetOwnership.NullableOpened(node, snapshot, permission)")]
        [Ensures("SortedSetOwnership.NullableRaw(node, snapshot, permission)")]
        internal static void CloseNullable<T>(SortedSet<T>.Node node, Ghost<SortedSetNullableSnapshot<T>> snapshot, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Ownership.nullable_null $(node) $(snapshot) $(permission)")]
        [Preserves("SortedSetOwnership.NullableRaw(node, snapshot, permission)")]
        [Requires("node == null")]
        [Ensures("!SortedSetOwnership.NullableRed(snapshot)")]
        internal static void NullCase<T>(SortedSet<T>.Node? node, Ghost<SortedSetNullableSnapshot<T>> snapshot, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Ownership.empty_owner #$(T) ()")]
        [Ensures("SortedSetOwnership.Owner(null, SortedSetOwnership.Empty<T>(), Perm.Full)")]
        internal static void Empty<T>() { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Ownership.consume_empty #$(T) ()")]
        [Requires("SortedSetOwnership.Owner(null, SortedSetOwnership.Empty<T>(), Perm.Full)")]
        internal static void ConsumeEmpty<T>() { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Ownership.retain_clear $(root) $(state)")]
        [Requires("SortedSetOwnership.Owner(root, state, Perm.Full)")]
        [Ensures("SortedSetOwnership.Owner(null, SortedSetOwnership.Cleared(state), Perm.Full)")]
        internal static void RetainClear<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.Ownership.retain_cell $(root) $(node) $(state) (hide $(snapshot))")]
        [Requires("SortedSetOwnership.Owner(root, state, Perm.Full)")]
        [Requires("SortedSetOwnership.Raw(node, snapshot, Perm.Full)")]
        [Ensures("SortedSetOwnership.Owner(root, SortedSetOwnership.RetiredCell(state, node, snapshot), Perm.Full)")]
        internal static void RetainCell<T>(SortedSet<T>.Node? root, SortedSet<T>.Node? node,
            SortedSetOwnershipState<T> state, Ghost<SortedSetNodeSnapshot<T>> snapshot) { }
    }
}
#endif
