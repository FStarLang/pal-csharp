using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("SortedSetInductive.Item.Spec.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Item.Point.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Item.fst")]
[assembly: IncludePulseFile("SortedSetInductive.Item.Set.fst")]

namespace System.Collections.Generic
{
    [SpecType("SortedSetInductive.Item.holder_snapshot")]
    internal readonly struct SortedSetHolderSnapshot<T> { }

    [SpecType("SortedSetInductive.Item.Set.ticket")]
    internal readonly struct SortedSetItemTicket<T> { }

    [SpecType("SortedSetInductive.Item.Set.result")]
    internal readonly struct SortedSetItemResult<T> { }

    internal static class SortedSetItem
    {
        [SpecOp("SortedSetInductive.Item.Set.holder_of")]
        internal static SortedSetHolderSnapshot<T> Holder<T>(SortedSetItemTicket<T> ticket) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.Set.node_of")]
        internal static SortedSetNodeSnapshot<T> Node<T>(SortedSetItemTicket<T> ticket) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.Set.model_of")]
        internal static SortedSetSnapshot<T> Model<T>(SortedSetItemTicket<T> ticket) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.Set.payload_of")]
        internal static SortedSetRetainedPayload<T> Payload<T>(SortedSetItemResult<T> result) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.Set.model_after")]
        internal static SortedSetSnapshot<T> After<T>(SortedSetItemResult<T> result) =>
            throw new InvalidOperationException();
        [SpecOp("Class_SortedSet.spec_SortedSet_SpecItems")]
        internal static Seq<T> Items<T>(SortedSetSnapshot<T> model) => throw new InvalidOperationException();
        [SpecOp("Class_SortedSet.spec_SortedSet_SpecComparer")]
        internal static IComparer<T> Comparer<T>(SortedSetSnapshot<T> model) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.Spec.position")]
        internal static int Position<T>(SortedSetLabels<T> tree, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.Spec.equivalent")]
        internal static bool Equivalent<T>(IComparer<T> comparer, T before, T after) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.Point.with_item")]
        internal static SortedSetNodeSnapshot<T> WithItem<T>(SortedSetNodeSnapshot<T> before, T item) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.Set.rest")]
        internal static SlProp Rest<T>([Plain] SortedSet<T> owner, SortedSet<T>.Node? node,
            SortedSetItemTicket<T> ticket) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.raw")]
        internal static SlProp Raw<T>([Plain] SortedSet<T> owner, SortedSetHolderSnapshot<T> before) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.with_state")]
        internal static SortedSetHolderSnapshot<T> WithState<T>(
            SortedSetHolderSnapshot<T> before, SortedSetRetainedPayload<T> payload) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.state_owner")]
        internal static SlProp StateOwner<T>(SortedSetHolderSnapshot<T> before, SortedSetRetainedPayload<T> payload) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.matches")]
        internal static bool Matches<T>(SortedSetHolderSnapshot<T> before,
            SortedSetRetainedPayload<T> payload, SortedSetSnapshot<T> model) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Item.pending")]
        internal static SlProp Pending<T>([Plain] SortedSet<T> owner, SortedSetHolderSnapshot<T> before,
            SortedSetRetainedPayload<T> payload, SortedSetSnapshot<T> model) =>
            throw new InvalidOperationException();
    }

    internal static class SortedSetItemProof
    {
        [Lemma, GhostArg("SortedSetSnapshot<T> snapshot"), GhostArg("TreeSet<T> owner")]
        [Requires("SortedSetOwnership.SetInv(owner, snapshot, Perm.Full)")]
        [Requires("SortedSetOwnership.Member(SortedSetOwnership.SnapshotLabels(snapshot), node)")]
        [Ensures("SortedSetOwnership.Raw(node, SortedSetItem.Node(Result), Perm.Full)")]
        [Ensures("SortedSetItem.Rest(owner, node, Result)")]
        [Ensures("Pal.Same(SortedSetItem.Model(Result), snapshot)")]
        [Ensures("SortedSetItem.Position(SortedSetOwnership.SnapshotLabels(snapshot), node) >= 0")]
        [Ensures("SortedSetItem.Position(SortedSetOwnership.SnapshotLabels(snapshot), node) < SortedSetItem.Items(snapshot).Length")]
        [Ensures("Pal.Same(SortedSetItem.Items(snapshot)[SortedSetItem.Position(SortedSetOwnership.SnapshotLabels(snapshot), node)], SortedSetOwnership.Item(SortedSetItem.Node(Result)))")]
        [PulseBody("SortedSetInductive.Item.Set.open_set $(owner) $(snapshot) $(node)")]
        internal static Ghost<SortedSetItemTicket<T>> Open<T>(SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();

        [Lemma, GhostArg("TreeSet<T> owner")]
        [Requires("SortedSetItem.Rest(owner, node, ticket)")]
        [Requires("SortedSetOwnership.Raw(node, SortedSetItem.WithItem(SortedSetItem.Node(ticket), item), Perm.Full)")]
        [Requires("SortedSetItem.Equivalent(SortedSetItem.Comparer(SortedSetItem.Model(ticket)), SortedSetOwnership.Item(SortedSetItem.Node(ticket)), item)")]
        [Ensures("SortedSetItem.Pending(owner, SortedSetItem.Holder(ticket), SortedSetItem.Payload(Result), SortedSetItem.After(Result))")]
        [Ensures("SortedSetItem.Comparer(SortedSetItem.After(Result)) == SortedSetItem.Comparer(SortedSetItem.Model(ticket))")]
        [Ensures("SortedSetItem.Position(SortedSetOwnership.SnapshotLabels(SortedSetItem.Model(ticket)), node) >= 0")]
        [Ensures("SortedSetItem.Position(SortedSetOwnership.SnapshotLabels(SortedSetItem.Model(ticket)), node) < SortedSetItem.Items(SortedSetItem.Model(ticket)).Length")]
        [Ensures("SortedSetItem.Items(SortedSetItem.After(Result)) == Pal.SetAt(SortedSetItem.Items(SortedSetItem.Model(ticket)), SortedSetItem.Position(SortedSetOwnership.SnapshotLabels(SortedSetItem.Model(ticket)), node), item)")]
        [PulseBody("SortedSetInductive.Item.Set.finish $(owner) $(node) $(ticket) $(item)")]
        internal static Ghost<SortedSetItemResult<T>> Finish<T>(SortedSet<T>.Node? node,
            Ghost<SortedSetItemTicket<T>> ticket, Ghost<T> item) => throw new InvalidOperationException();

        [Lemma, Conditional("PAL")]
        [Requires("SortedSetItem.Pending(owner, before, payload, model)")]
        [Ensures("SortedSetItem.Raw(owner, before)")]
        [Ensures("SortedSetItem.StateOwner(before, payload)")]
        [Ensures("SortedSetItem.Matches(before, payload, model)")]
        [PulseBody("SortedSetInductive.Item.open_pending $(owner) $(before) $(payload) $(model)")]
        internal static void OpenPending<T>([Plain] TreeSet<T> owner, Ghost<SortedSetRetainedPayload<T>> payload,
            Ghost<SortedSetHolderSnapshot<T>> before, Ghost<SortedSetSnapshot<T>> model) { }

        [Lemma, Conditional("PAL")]
        [Requires("SortedSetItem.Raw(owner, SortedSetItem.WithState(before, payload))")]
        [Requires("SortedSetItem.StateOwner(before, payload)")]
        [Requires("SortedSetItem.Matches(before, payload, model)")]
        [Ensures("SortedSetOwnership.SetInv(owner, model, Perm.Full)")]
        [PulseBody("SortedSetInductive.Item.close_committed $(owner) $(before) $(payload) $(model)")]
        internal static void CloseCommitted<T>([Plain] TreeSet<T> owner, Ghost<SortedSetHolderSnapshot<T>> before,
            Ghost<SortedSetRetainedPayload<T>> payload, Ghost<SortedSetSnapshot<T>> model) { }
    }

    public partial class SortedSet<T>
    {
        // This is an emitted stateful helper, not a SpecOp. Its only source store
        // updates the erased ownership witness after the real Item write.
        [System.Diagnostics.Conditional("PAL")]
        [GhostArg("SortedSetHolderSnapshot<T> before"), GhostArg("SortedSetSnapshot<T> model")]
        [GhostArg("SortedSetRetainedPayload<T> payload")]
        [Requires("SortedSetItem.Pending(owner, before, payload, model)")]
        [Ensures("SortedSetOwnership.SetInv(owner, model, Perm.Full)")]
        internal static void CommitItemState([Plain] TreeSet<T> owner)
        {
            Ghost<SortedSetRetainedPayload<T>> payload = default;
            Pal.Capture(ref payload, Pal.Ghost<SortedSetRetainedPayload<T>>("payload"));
            SortedSetItemProof.OpenPending(owner, payload, Pal.Ghost<SortedSetHolderSnapshot<T>>("before"),
                Pal.Ghost<SortedSetSnapshot<T>>("model"));
            Pal.UpdateGhost(ref owner.ownershipState, SortedSetRetainedHolder.State(payload.Value));
            SortedSetItemProof.CloseCommitted(owner, Pal.Ghost<SortedSetHolderSnapshot<T>>("before"),
                payload, Pal.Ghost<SortedSetSnapshot<T>>("model"));
        }
    }
}
