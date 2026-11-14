#if PAL
using System;
using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetFrontier
    {
        [SpecOp("SortedSetInductive.MergeFrontier.read_facts")]
        internal static void Read2Facts<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDownRemove.is2")]
        internal static bool Is2<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.MergeFrontier.after")]
        internal static SlProp MergeAfter<T>(SortedSet<T>.Node? node, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Remove.merged")]
        internal static SortedSetLabels<T> Merged<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Frontier.snapshot")]
        internal static SortedSetNodeSnapshot<T> Snapshot<T>(SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Frontier.read_cells")]
        internal static SlProp ReadCells<T>(SortedSet<T>.Node? node, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Frontier.split_cells")]
        internal static SlProp SplitCells<T>(SortedSet<T>.Node? node, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Frontier.split_after")]
        internal static SlProp SplitAfter<T>(SortedSet<T>.Node? node, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.is4")]
        internal static bool Is4<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Insert.split_tree")]
        internal static SortedSetLabels<T> Split<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Frontier.read_facts")]
        internal static void ReadFacts<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Frontier.optional_at")]
        internal static SortedSetNullableSnapshot<T> OptionalAt<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Frontier.optional_rest")]
        internal static SlProp OptionalRest<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();
    }

    internal static class SortedSetFrontierProof
    {
        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Member(labels, node) && SortedSetLocal.Branch(SortedSetLocal.Left(SortedSetEdit.Sub(labels, node))) && SortedSetLocal.Branch(SortedSetLocal.Right(SortedSetEdit.Sub(labels, node)))")]
        [Ensures("SortedSetFrontier.SplitCells(node, SortedSetEdit.Sub(labels, node))")]
        [Ensures("SortedSetEdit.Pending(labels, node)")]
        [PulseBody("SortedSetInductive.MergeFrontier.open_merge $(labels) $(node)")]
        internal static void OpenMerge<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [Lemma]
        [Requires("SortedSetFrontier.MergeAfter(node, SortedSetEdit.Sub(labels, node))")]
        [Requires("SortedSetEdit.Pending(labels, node)")]
        [Requires("SortedSetOwnership.Member(labels, node) && SortedSetLocal.Branch(SortedSetLocal.Left(SortedSetEdit.Sub(labels, node))) && SortedSetLocal.Branch(SortedSetLocal.Right(SortedSetEdit.Sub(labels, node)))")]
        [Ensures("SortedSetOwnership.Owns(SortedSetFrontier.Merged(labels, node), Perm.Full)")]
        [PulseBody("SortedSetInductive.MergeFrontier.close_merge $(labels) $(node)")]
        internal static void CloseMerge<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Good(labels) && (node == null || SortedSetOwnership.Member(labels, node))")]
        [Ensures("SortedSetOwnership.NullableRaw(node, SortedSetFrontier.OptionalAt(labels, node), Perm.Full)")]
        [Ensures("SortedSetFrontier.OptionalRest(labels, node)")]
        [Ensures("SortedSetOwnership.NullableRed(SortedSetFrontier.OptionalAt(labels, node)) == SortedSetEdit.NodeRed(labels, node)")]
        [PulseBody("SortedSetInductive.Frontier.open_optional_at $(labels) $(node)")]
        internal static void OpenOptional<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [Lemma]
        [Requires("SortedSetOwnership.NullableRaw(node, SortedSetFrontier.OptionalAt(labels, node), Perm.Full)")]
        [Requires("SortedSetFrontier.OptionalRest(labels, node)")]
        [Requires("SortedSetOwnership.Good(labels) && (node == null || SortedSetOwnership.Member(labels, node))")]
        [Ensures("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [PulseBody("SortedSetInductive.Frontier.close_optional_at $(labels) $(node)")]
        internal static void CloseOptional<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Good(labels) && SortedSetOwnership.Member(labels, node)")]
        [Ensures("SortedSetFrontier.ReadCells(node, SortedSetEdit.Sub(labels, node))")]
        [Ensures("SortedSetEdit.Pending(labels, node)")]
        [PulseBody("SortedSetInductive.Frontier.open_read $(labels) $(node)")]
        internal static void OpenRead<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [Lemma]
        [Requires("SortedSetFrontier.ReadCells(node, SortedSetEdit.Sub(labels, node))")]
        [Requires("SortedSetEdit.Pending(labels, node)")]
        [Requires("SortedSetOwnership.Member(labels, node)")]
        [Ensures("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [PulseBody("SortedSetInductive.Frontier.close_read $(labels) $(node)")]
        internal static void CloseRead<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Member(labels, node) && SortedSetFrontier.Is4(SortedSetEdit.Sub(labels, node))")]
        [Ensures("SortedSetFrontier.SplitCells(node, SortedSetEdit.Sub(labels, node))")]
        [Ensures("SortedSetEdit.Pending(labels, node)")]
        [PulseBody("SortedSetInductive.Frontier.open_split $(labels) $(node)")]
        internal static void OpenSplit<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [Lemma]
        [Requires("SortedSetFrontier.SplitAfter(node, SortedSetEdit.Sub(labels, node))")]
        [Requires("SortedSetEdit.Pending(labels, node)")]
        [Requires("SortedSetOwnership.Member(labels, node) && SortedSetFrontier.Is4(SortedSetEdit.Sub(labels, node))")]
        [Ensures("SortedSetOwnership.Owns(SortedSetFrontier.Split(labels, node), Perm.Full)")]
        [PulseBody("SortedSetInductive.Frontier.close_split $(labels) $(node)")]
        internal static void CloseSplit<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }
    }
}
#endif
