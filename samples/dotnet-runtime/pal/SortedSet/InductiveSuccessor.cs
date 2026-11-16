using System;
using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetLocal
    {
        [SpecOp("Pulse.Lib.CSharp.Tree.left")]
        internal static SortedSetLabels<T> Left<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.Tree.right")]
        internal static SortedSetLabels<T> Right<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.Tree.Branch?")]
        internal static bool Branch<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.recolorn")]
        internal static SortedSetLabels<T> Color<T>(SortedSetLabels<T> labels, bool red) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.nred")]
        internal static bool Red<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Local.opened")]
        internal static SlProp Opened<T>(SortedSet<T>.Node? node, SortedSetLabels<T> labels) => throw new InvalidOperationException();
    }

    internal static class SortedSetLocalProof
    {
        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetLocal.Branch(labels) && node == SortedSetOwnership.Top(labels)")]
        [Ensures("SortedSetLocal.Opened(node, labels)")]
        [Ensures("node != null")]
        [PulseBody("SortedSetInductive.Local.open_node $(node) $(labels)")]
        internal static void Open<T>(SortedSet<T>.Node? node, Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetLocal.Opened(node, labels)")]
        [Ensures("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Ensures("node == SortedSetOwnership.Top(labels)")]
        [PulseBody("SortedSetInductive.Local.close_node $(node) $(labels)")]
        internal static void Close<T>(SortedSet<T>.Node? node, Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(SortedSetLocal.Left(labels), Perm.Full)")]
        [Requires("SortedSetOwnership.Owns(SortedSetLocal.Right(labels), Perm.Full)")]
        [Requires("SortedSetLocal.Branch(labels)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLocal.Left(SortedSetLocal.Color(labels, false)), Perm.Full)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLocal.Right(SortedSetLocal.Color(labels, false)), Perm.Full)")]
        [PulseBody("SortedSetInductive.Local.color_leaves $(labels) false")]
        internal static void BlackLeaves<T>(Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(SortedSetLocal.Left(labels), Perm.Full)")]
        [Requires("SortedSetOwnership.Owns(SortedSetLocal.Right(labels), Perm.Full)")]
        [Requires("SortedSetLocal.Branch(labels)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLocal.Left(SortedSetLocal.Color(labels, red)), Perm.Full)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLocal.Right(SortedSetLocal.Color(labels, red)), Perm.Full)")]
        [PulseBody("SortedSetInductive.Local.color_leaves $(labels) $(red)")]
        internal static void ColorLeaves<T>(Ghost<SortedSetLabels<T>> labels, bool red) { }
    }

    internal static class SortedSetSuccessor
    {
        [SpecOp("Pulse.Lib.CSharp.TopDownSucc.pre_col")]
        internal static SortedSetLabels<T> PreColor<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Successor.replaced")]
        internal static SortedSetLabels<T> Replacement<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Successor.remaining")]
        internal static SortedSetLabels<T> Remaining<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDownSucc.succ_of")]
        internal static SortedSet<T>.Node? Successor<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDownSucc.pos_of")]
        internal static SortedSet<T>.Node? ParentOfSuccessor<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Successor.layout")]
        internal static bool Layout<T>(SortedSetLabels<T> labels, SortedSet<T>.Node successor, SortedSet<T>.Node? parent) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Successor.cell")]
        internal static SlProp Cell<T>(SortedSet<T>.Node node, SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDownSucc.rdel")]
        internal static SortedSetLabels<T> Delete<T>(SortedSetLabels<T> labels, SortedSet<T>.Node match) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Frontier.snapshot")]
        internal static SortedSetNodeSnapshot<T> Snapshot<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Successor.matches")]
        internal static bool Matches<T>(SortedSetLabels<T> labels, SortedSetNodeSnapshot<T> snapshot) => throw new InvalidOperationException();
    }

    internal static class SortedSetSuccessorProof
    {
        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Good(labels) && SortedSetLocal.Branch(labels)")]
        [Requires("successor == SortedSetSuccessor.Successor(labels)")]
        [Requires("Pal.Implies(SortedSetLocal.Branch(SortedSetLocal.Right(labels)), parent == SortedSetSuccessor.ParentOfSuccessor(labels))")]
        [Ensures("SortedSetSuccessor.Layout(labels, successor, parent)")]
        [PulseBody("SortedSetInductive.Successor.layout_lemma $(labels) $(successor) $(parent)")]
        internal static void Layout<T>(SortedSet<T>.Node successor, SortedSet<T>.Node? parent, Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("!SortedSetLocal.Branch(labels)")]
        [Ensures("true")]
        [PulseBody("SortedSetInductive.Successor.empty $(labels)")]
        internal static void Empty<T>(Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(SortedSetLocal.Left(labels), Perm.Full)")]
        [Requires("SortedSetOwnership.Owns(SortedSetLocal.Right(labels), Perm.Full)")]
        [Requires("SortedSetLocal.Branch(labels) && !SortedSetLocal.Branch(SortedSetLocal.Right(labels))")]
        [Ensures("SortedSetOwnership.Owns(SortedSetSuccessor.PreColor(labels), Perm.Full)")]
        [PulseBody("SortedSetInductive.Successor.no_right $(labels)")]
        internal static void NoRight<T>(Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(SortedSetLocal.Left(labels), Perm.Full)")]
        [Requires("SortedSetOwnership.Owns(SortedSetSuccessor.Remaining(labels), Perm.Full)")]
        [Requires("SortedSetLocal.Branch(labels) && SortedSetLocal.Branch(SortedSetLocal.Right(labels))")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLocal.Left(SortedSetSuccessor.PreColor(labels)), Perm.Full)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLocal.Right(SortedSetSuccessor.PreColor(labels)), Perm.Full)")]
        [PulseBody("SortedSetInductive.Successor.successor_leaves $(labels)")]
        internal static void Leaves<T>(Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetSuccessor.Cell(node, labels)")]
        [Requires("SortedSetSuccessor.Matches(labels, snapshot)")]
        [Ensures("SortedSetOwnership.Raw(node, snapshot, Perm.Full)")]
        [PulseBody("SortedSetInductive.Successor.canonical_cell $(node) $(labels) $(snapshot)")]
        internal static void Canonical<T>(SortedSet<T>.Node node,
            Ghost<SortedSetLabels<T>> labels, Ghost<SortedSetNodeSnapshot<T>> snapshot) { }
    }
}
