#if PAL
using System;
using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetDispatch
    {
        [SpecOp("SortedSetInductive.Rotation.child")]
        internal static SortedSetLabels<T> Child<T>(SortedSetLabels<T> labels, bool direction) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Selector.window")]
        internal static SlProp Selector<T>(SortedSet<T>.Node? root, SortedSet<T>.Node? sibling, SortedSetLabels<T> labels, bool direction) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveRotation.can_rotate")]
        internal static bool CanRotate<T>(TreeRotation rotation, SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDownRemove.rotn")]
        internal static SortedSetLabels<T> Rotated<T>(TreeRotation rotation, SortedSetLabels<T> labels) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveDispatch.before")]
        internal static SlProp Before<T>(SortedSet<T>.Node? root, SortedSetLabels<T> labels, TreeRotation rotation) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveDispatch.after")]
        internal static SlProp After<T>(SortedSet<T>.Node? root, SortedSet<T>.Node? pivot, SortedSetLabels<T> labels, TreeRotation rotation) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.RemoveDispatch.after_color")]
        internal static SlProp AfterColor<T>(SortedSet<T>.Node? root, SortedSet<T>.Node? pivot, SortedSetLabels<T> labels, TreeRotation rotation, bool red) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Borrow.colored")]
        internal static SortedSetLabels<T> Colored<T>(SortedSetLabels<T> labels, TreeRotation rotation) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Borrow.blackened")]
        internal static SortedSetLabels<T> Blackened<T>(SortedSetLabels<T> labels, TreeRotation rotation) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Borrow.borrowed")]
        internal static SortedSetLabels<T> Borrowed<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? current, TreeRotation rotation) => throw new InvalidOperationException();
    }

    internal static class SortedSetDispatchProof
    {
        [Lemma]
        [Requires("SortedSetDispatch.AfterColor(root, pivot, labels, rotation, true)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetDispatch.Colored(labels, rotation), Perm.Full)")]
        [Ensures("pivot == SortedSetOwnership.Top(SortedSetDispatch.Colored(labels, rotation))")]
        [PulseBody("SortedSetInductive.RemoveDispatch.close_colored $(root) $(pivot) $(labels) $(rotation) true")]
        internal static void CloseRed<T>(SortedSet<T>.Node? root, SortedSet<T>.Node? pivot,
            Ghost<SortedSetLabels<T>> labels, TreeRotation rotation) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("root == SortedSetOwnership.Top(labels) && sibling == SortedSetOwnership.Top(SortedSetDispatch.Child(labels, direction)) && SortedSetLocal.Branch(labels) && SortedSetLocal.Branch(SortedSetDispatch.Child(labels, direction))")]
        [Ensures("SortedSetDispatch.Selector(root, sibling, labels, direction)")]
        [PulseBody("SortedSetInductive.Selector.open_selector $(root) $(sibling) $(labels) $(direction)")]
        internal static void OpenSelector<T>(SortedSet<T>.Node? root, SortedSet<T>.Node? sibling,
            Ghost<SortedSetLabels<T>> labels, Ghost<bool> direction) { }

        [Lemma]
        [Requires("SortedSetDispatch.Selector(root, sibling, labels, direction)")]
        [Ensures("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [PulseBody("SortedSetInductive.Selector.close_selector $(root) $(sibling) $(labels) $(direction)")]
        internal static void CloseSelector<T>(SortedSet<T>.Node? root, Ghost<SortedSet<T>.Node?> sibling,
            Ghost<SortedSetLabels<T>> labels, Ghost<bool> direction) { }

        [Lemma]
        [Requires("SortedSetDispatch.Before(root, labels, rotation)")]
        [Requires("false")]
        [Ensures("SortedSetDispatch.After(root, null, labels, rotation)")]
        [Ensures("false")]
        [PulseBody("SortedSetInductive.RemoveDispatch.impossible $(root) $(labels) $(rotation)")]
        internal static void Impossible<T>(SortedSet<T>.Node? root, Ghost<SortedSetLabels<T>> labels,
            TreeRotation rotation) { }

        [Lemma]
        [Requires("SortedSetDispatch.Before(root, labels, from)")]
        [Requires("from == into")]
        [Ensures("SortedSetDispatch.Before(root, labels, into)")]
        [PulseBody("SortedSetInductive.RemoveDispatch.specialize $(root) $(labels) $(from) $(into)")]
        internal static void Specialize<T>(SortedSet<T>.Node? root, Ghost<SortedSetLabels<T>> labels,
            TreeRotation from, TreeRotation into) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("root == SortedSetOwnership.Top(labels) && SortedSetDispatch.CanRotate(rotation, labels)")]
        [Ensures("SortedSetDispatch.Before(root, labels, rotation)")]
        [PulseBody("SortedSetInductive.RemoveDispatch.open_dispatch $(root) $(labels) $(rotation)")]
        internal static void Open<T>(SortedSet<T>.Node? root, Ghost<SortedSetLabels<T>> labels, TreeRotation rotation) { }

        [Lemma]
        [Requires("SortedSetDispatch.After(root, pivot, labels, rotation)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetDispatch.Rotated(rotation, labels), Perm.Full)")]
        [Ensures("pivot == SortedSetOwnership.Top(SortedSetDispatch.Rotated(rotation, labels))")]
        [PulseBody("SortedSetInductive.RemoveDispatch.close_dispatch $(root) $(pivot) $(labels) $(rotation)")]
        internal static void Close<T>(SortedSet<T>.Node? root, SortedSet<T>.Node? pivot,
            Ghost<SortedSetLabels<T>> labels, TreeRotation rotation) { }
    }
}
#endif
