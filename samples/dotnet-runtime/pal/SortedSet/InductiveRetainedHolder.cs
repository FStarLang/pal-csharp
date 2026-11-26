using System;
using PalLang;

namespace System.Collections.Generic
{
    [SpecType("SortedSetInductive.RetainedHolder.payload")]
    internal readonly struct SortedSetRetainedPayload<T> { }

    internal static class SortedSetRetainedHolder
    {
        [SpecOp("SortedSetInductive.RetainedHolder.payload_of")]
        internal static SortedSetRetainedPayload<T> Payload<T>(SortedSetOwnershipState<T> state) =>
            throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.RetainedHolder.state_of")]
        internal static SortedSetOwnershipState<T> State<T>(SortedSetRetainedPayload<T> payload) =>
            throw new InvalidOperationException();
    }

    internal static class SortedSetRetainedHolderProof
    {
        [Lemma, GhostArg("SortedSetSnapshot<T> snapshot"), GhostArg("SortedSet<T>.Node? previous")]
        [Requires("SortedSetOwnership.Owner(previous, oldState, Perm.Full)")]
        [Requires("SortedSetOwnership.SetInv(dummy, snapshot, Perm.Full)")]
        [Requires("adopted == SortedSetOwnership.Top(SortedSetOwnership.SnapshotLabels(snapshot))")]
        [Ensures("SortedSetOwnership.Owner(adopted, SortedSetRetainedHolder.State(Result), Perm.Full)")]
        [Ensures("Pal.Same(SortedSetOwnership.Active(SortedSetRetainedHolder.State(Result)), SortedSetOwnership.SnapshotLabels(snapshot))")]
        [PulseBody("SortedSetInductive.RetainedHolder.transfer_payload $(previous) $(oldState) $(dummy) $(snapshot) $(adopted)")]
        internal static Ghost<SortedSetRetainedPayload<T>> Transfer<T>(
            Ghost<SortedSet<T>.Node?> adopted, Ghost<SortedSetOwnershipState<T>> oldState,
            [Plain, Consumes] SortedSet<T> dummy) => throw new InvalidOperationException();
    }
}
