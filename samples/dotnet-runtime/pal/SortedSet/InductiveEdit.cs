using System;
using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetEdit
    {
        [SpecOp("SortedSetInductive.Ownership.replace")]
        internal static SortedSetOwnershipState<T> ReplaceState<T>(
            SortedSetOwnershipState<T> state, Ghost<SortedSetLabels<T>> labels) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Edit.retained")]
        internal static SlProp Retained<T>(SortedSetOwnershipState<T> state) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Relink.replace")]
        internal static SortedSetLabels<T> Replace<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node,
            SortedSetLabels<T> replacement) => throw new InvalidOperationException();

        [SpecOp("Pulse.Lib.CSharp.RegionPath.sub")]
        internal static SortedSetLabels<T> Sub<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Relink.parent")]
        internal static SortedSet<T>.Node? Parent<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node) =>
            throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Relink.pending")]
        internal static SlProp Pending<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Relink.cell")]
        internal static SlProp ParentCell<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node,
            SortedSet<T>.Node? parent, SortedSet<T>.Node? hole) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Mutation.recolor")]
        internal static SortedSetLabels<T> Recolor<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node, bool red) =>
            throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Mutation.node_red")]
        internal static bool NodeRed<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Mutation.color_opened")]
        internal static SlProp ColorOpened<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node, bool red) =>
            throw new InvalidOperationException();
    }

    internal static class SortedSetEditProof
    {
        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Preserves("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Ensures("SortedSetOwnership.Good(labels)")]
        [PulseBody("SortedSetInductive.Edit.facts $(labels)")]
        internal static void Facts<T>(Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Member(labels, node)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetEdit.Sub(labels, node), Perm.Full)")]
        [Ensures("SortedSetEdit.Pending(labels, node)")]
        [PulseBody("SortedSetInductive.Relink.cut $(labels) $(node)")]
        internal static void Cut<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node node) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(before, Perm.Full)")]
        [Requires("Pal.Same(before, after)")]
        [Ensures("SortedSetOwnership.Owns(after, Perm.Full)")]
        [PulseBody("SortedSetInductive.Edit.change $(before) $(after)")]
        internal static void Change<T>(Ghost<SortedSetLabels<T>> before, Ghost<SortedSetLabels<T>> after) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Good(labels) && SortedSetOwnership.Member(labels, node)")]
        [Ensures("SortedSetEdit.ColorOpened(labels, node, SortedSetEdit.NodeRed(labels, node))")]
        [Ensures("node != null")]
        [PulseBody("SortedSetInductive.Mutation.open_color $(labels) $(node)")]
        internal static void OpenColor<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetEdit.ColorOpened(labels, node, red)")]
        [Requires("node != null")]
        [Ensures("SortedSetOwnership.Owns(SortedSetEdit.Recolor(labels, node, red), Perm.Full)")]
        [PulseBody("SortedSetInductive.Mutation.close_color $(labels) $(node) $(red)")]
        internal static void CloseColor<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node, bool red) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetEdit.ColorOpened(labels, node, true)")]
        [Requires("node != null")]
        [Ensures("SortedSetOwnership.Owns(SortedSetEdit.Recolor(labels, node, true), Perm.Full)")]
        [PulseBody("SortedSetInductive.Mutation.close_color $(labels) $(node) true")]
        internal static void CloseRed<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetEdit.ColorOpened(labels, node, false)")]
        [Requires("node != null")]
        [Ensures("SortedSetOwnership.Owns(SortedSetEdit.Recolor(labels, node, false), Perm.Full)")]
        [PulseBody("SortedSetInductive.Mutation.close_color $(labels) $(node) false")]
        internal static void CloseBlack<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? node) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetEdit.Pending(labels, child)")]
        [Requires("SortedSetOwnership.Good(labels) && SortedSetOwnership.Member(labels, child)")]
        [Requires("parent == SortedSetEdit.Parent(labels, child) && parent != null")]
        [Ensures("SortedSetEdit.ParentCell(labels, child, parent, child)")]
        [PulseBody("SortedSetInductive.Relink.open_parent $(labels) $(child) $(parent)")]
        internal static void OpenParent<T>(Ghost<SortedSetLabels<T>> labels,
            SortedSet<T>.Node child, SortedSet<T>.Node parent) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetEdit.ParentCell(labels, child, parent, SortedSetOwnership.Top(replacement))")]
        [Requires("SortedSetOwnership.Owns(replacement, Perm.Full)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetEdit.Replace(labels, child, replacement), Perm.Full)")]
        [Ensures("SortedSetOwnership.Top(SortedSetEdit.Replace(labels, child, replacement)) == SortedSetOwnership.Top(labels)")]
        [PulseBody("SortedSetInductive.Relink.close_parent $(labels) $(child) $(parent) $(replacement)")]
        internal static void CloseParent<T>(Ghost<SortedSetLabels<T>> labels,
            SortedSet<T>.Node child, SortedSet<T>.Node parent, Ghost<SortedSetLabels<T>> replacement) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetEdit.Pending(labels, child)")]
        [Requires("SortedSetOwnership.Owns(replacement, Perm.Full)")]
        [Requires("SortedSetOwnership.Good(labels) && SortedSetOwnership.Member(labels, child)")]
        [Requires("SortedSetEdit.Parent(labels, child) == null")]
        [Ensures("SortedSetOwnership.Owns(SortedSetEdit.Replace(labels, child, replacement), Perm.Full)")]
        [Ensures("SortedSetOwnership.Top(SortedSetEdit.Replace(labels, child, replacement)) == SortedSetOwnership.Top(replacement)")]
        [PulseBody("SortedSetInductive.Relink.close_root $(labels) $(child) $(replacement)")]
        internal static void CloseRoot<T>(Ghost<SortedSetLabels<T>> labels,
            SortedSet<T>.Node child, Ghost<SortedSetLabels<T>> replacement) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owner(root, state, Perm.Full)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetOwnership.Active(state), Perm.Full)")]
        [Ensures("SortedSetEdit.Retained(state)")]
        [Ensures("root == SortedSetOwnership.Top(SortedSetOwnership.Active(state))")]
        [PulseBody("SortedSetInductive.Edit.begin_owner $(root) $(state)")]
        internal static void BeginOwner<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> state) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetEdit.Retained(state)")]
        [Requires("root == SortedSetOwnership.Top(labels)")]
        [Ensures("SortedSetOwnership.Owner(root, SortedSetEdit.ReplaceState(state, labels), Perm.Full)")]
        [PulseBody("SortedSetInductive.Edit.end_owner $(root) $(state) (hide $(labels))")]
        internal static void EndOwner<T>(SortedSet<T>.Node? root,
            SortedSetOwnershipState<T> state, Ghost<SortedSetLabels<T>> labels) { }
    }
}
