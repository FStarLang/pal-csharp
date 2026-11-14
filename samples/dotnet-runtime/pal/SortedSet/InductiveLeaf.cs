using System;
using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetLeaf
    {
        [SpecOp("Pulse.Lib.CSharp.TopDown.leaf")]
        internal static SortedSetLabels<T> Red<T>(SortedSet<T>.Node? node, T item) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Leaf.black_leaf")]
        internal static SortedSetLabels<T> Black<T>(SortedSet<T>.Node? node, T item) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Leaf.linked")]
        internal static SortedSetLabels<T> Linked<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? parent,
            SortedSet<T>.Node? node, T item, bool right) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Local.opened")]
        internal static SlProp Opened<T>(SortedSet<T>.Node? node, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Leaf.link_slot")]
        internal static SlProp Slot<T>(SortedSet<T>.Node? parent, SortedSetLabels<T> labels, SortedSet<T>.Node? node, bool right) =>
            throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.Tree.left")]
        internal static SortedSetLabels<T> Left<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.Tree.right")]
        internal static SortedSetLabels<T> Right<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.Tree.Branch?")]
        internal static bool Branch<T>(SortedSetLabels<T> labels) => throw new InvalidOperationException();
    }

    internal static class SortedSetLeafProof
    {
        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Good(labels) && SortedSetOwnership.Top(labels) == null")]
        [Ensures("!SortedSetLeaf.Branch(labels)")]
        [PulseBody("SortedSetInductive.Leaf.release_empty $(labels)")]
        internal static void ReleaseEmpty<T>(Ghost<SortedSetLabels<T>> labels) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Fresh(node, item, NodeColor.Black)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLeaf.Black(node, item), Perm.Full)")]
        [PulseBody("SortedSetInductive.Leaf.make_leaf $(node) $(item) false")]
        internal static void MakeBlack<T>(SortedSet<T>.Node node, T item) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Fresh(node, item, NodeColor.Red)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLeaf.Red(node, item), Perm.Full)")]
        [PulseBody("SortedSetInductive.Leaf.make_leaf $(node) $(item) true")]
        internal static void MakeRed<T>(SortedSet<T>.Node node, T item) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Preserves("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Preserves("SortedSetOwnership.Owns(SortedSetLeaf.Red(node, item), Perm.Full)")]
        [Ensures("!SortedSetOwnership.Member(labels, node)")]
        [PulseBody("SortedSetInductive.Leaf.fresh $(labels) $(node) $(item)")]
        internal static void Fresh<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node node, T item) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Good(labels) && SortedSetOwnership.Member(labels, parent)")]
        [Ensures("SortedSetLeaf.Opened(parent, SortedSetEdit.Sub(labels, parent))")]
        [Ensures("SortedSetEdit.Pending(labels, parent)")]
        [PulseBody("SortedSetInductive.Leaf.open_link $(labels) $(parent)")]
        internal static void OpenLink<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? parent) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetLeaf.Slot(parent, SortedSetEdit.Sub(labels, parent), node, true)")]
        [Requires("SortedSetOwnership.Owns(SortedSetLeaf.Red(node, item), Perm.Full)")]
        [Requires("SortedSetEdit.Pending(labels, parent)")]
        [Requires("!SortedSetLeaf.Branch(SortedSetLeaf.Right(SortedSetEdit.Sub(labels, parent)))")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLeaf.Linked(labels, parent, node, item, true), Perm.Full)")]
        [PulseBody("SortedSetInductive.Leaf.close_link $(labels) $(parent) $(node) $(item) true")]
        internal static void CloseRight<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? parent,
            SortedSet<T>.Node node, T item) { }

        [System.Diagnostics.Conditional("PAL")]
        [Lemma]
        [Requires("SortedSetLeaf.Slot(parent, SortedSetEdit.Sub(labels, parent), node, false)")]
        [Requires("SortedSetOwnership.Owns(SortedSetLeaf.Red(node, item), Perm.Full)")]
        [Requires("SortedSetEdit.Pending(labels, parent)")]
        [Requires("!SortedSetLeaf.Branch(SortedSetLeaf.Left(SortedSetEdit.Sub(labels, parent)))")]
        [Ensures("SortedSetOwnership.Owns(SortedSetLeaf.Linked(labels, parent, node, item, false), Perm.Full)")]
        [PulseBody("SortedSetInductive.Leaf.close_link $(labels) $(parent) $(node) $(item) false")]
        internal static void CloseLeft<T>(Ghost<SortedSetLabels<T>> labels, SortedSet<T>.Node? parent,
            SortedSet<T>.Node node, T item) { }
    }
}
