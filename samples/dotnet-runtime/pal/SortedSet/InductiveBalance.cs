#if PAL
using System;
using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetBalance
    {
        [SpecOp("SortedSetInductive.Rotation.single_ignored")]
        internal static SlProp SingleIgnored<T>(SortedSet<T>.Node root, SortedSetLabels<T> labels, bool right) =>
            throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.balance_ready")]
        internal static bool Ready<T>(SortedSetLabels<T> labels, SortedSet<T>.Node current,
            SortedSet<T>.Node? parent, SortedSet<T>.Node grandParent, SortedSet<T>.Node? greatGrandParent) =>
            throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.balance")]
        internal static SortedSetLabels<T> Balanced<T>(SortedSetLabels<T> labels, SortedSet<T>.Node current) =>
            throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.balance_sub")]
        internal static SortedSetLabels<T> SubBalanced<T>(bool currentRight, bool parentRight, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.rot_for")]
        internal static SortedSetLabels<T> Rotated<T>(bool currentRight, bool parentRight, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.TopDown.same_side")]
        internal static bool SameSide<T>(SortedSetLabels<T> labels, SortedSet<T>.Node current) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Balance.current_right")]
        internal static bool CurrentRight<T>(SortedSetLabels<T> labels, SortedSet<T>.Node current, SortedSet<T>.Node? parent) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Balance.parent_right")]
        internal static bool ParentRight<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? parent, SortedSet<T>.Node grandParent) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Balance.can_rotate")]
        internal static bool CanRotate<T>(bool currentRight, bool parentRight, SortedSetLabels<T> labels) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Balance.layout")]
        internal static void Layout<T>(SortedSetLabels<T> labels, SortedSet<T>.Node current,
            SortedSet<T>.Node? parent, SortedSet<T>.Node grandParent, SortedSet<T>.Node? greatGrandParent) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Balance.rotated_facts")]
        internal static void RotatedFacts<T>(SortedSetLabels<T> labels, bool currentRight, bool parentRight) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Balance.top_color")]
        internal static void TopColor<T>(SortedSetLabels<T> labels, SortedSet<T>.Node? node, bool red) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Balance.balance_result")]
        internal static void Result<T>(SortedSetLabels<T> labels, bool currentRight, bool parentRight) =>
            throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Rotation.single_before")]
        internal static SlProp SingleBefore<T>(SortedSet<T>.Node root, SortedSetLabels<T> labels, bool right) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Rotation.single_after")]
        internal static SlProp SingleAfter<T>(SortedSet<T>.Node root, SortedSet<T>.Node pivot, SortedSetLabels<T> labels, bool right) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Rotation.single")]
        internal static SortedSetLabels<T> Single<T>(SortedSetLabels<T> labels, bool right) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Rotation.double_before")]
        internal static SlProp DoubleBefore<T>(SortedSet<T>.Node root, SortedSetLabels<T> labels, bool right) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Rotation.double_after")]
        internal static SlProp DoubleAfter<T>(SortedSet<T>.Node root, SortedSet<T>.Node pivot, SortedSetLabels<T> labels, bool right) =>
            throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Rotation.double")]
        internal static SortedSetLabels<T> Double<T>(SortedSetLabels<T> labels, bool right) => throw new InvalidOperationException();
    }

    internal static class SortedSetBalanceProof
    {
        [Lemma]
        [Requires("SortedSetBalance.SingleIgnored(root, labels, true)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetBalance.Single(labels, true), Perm.Full)")]
        [PulseBody("SortedSetInductive.Rotation.close_ignored $(root) $(labels) true")]
        internal static void CloseIgnoredLeft<T>(SortedSet<T>.Node root, Ghost<SortedSetLabels<T>> labels) { }

        [Lemma]
        [Requires("SortedSetBalance.SingleIgnored(root, labels, false)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetBalance.Single(labels, false), Perm.Full)")]
        [PulseBody("SortedSetInductive.Rotation.close_ignored $(root) $(labels) false")]
        internal static void CloseIgnoredRight<T>(SortedSet<T>.Node root, Ghost<SortedSetLabels<T>> labels) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("root == SortedSetOwnership.Top(labels) && SortedSetBalance.CanRotate(true, true, labels)")]
        [Ensures("SortedSetBalance.SingleBefore(root, labels, true)")]
        [PulseBody("SortedSetInductive.Rotation.open_single $(root) $(labels) true")]
        internal static void OpenLeft<T>(SortedSet<T>.Node root, Ghost<SortedSetLabels<T>> labels) { }

        [Lemma]
        [Requires("SortedSetBalance.SingleAfter(root, pivot, labels, true)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetBalance.Single(labels, true), Perm.Full)")]
        [Ensures("pivot == SortedSetOwnership.Top(SortedSetBalance.Single(labels, true))")]
        [PulseBody("SortedSetInductive.Rotation.close_single $(root) $(pivot) $(labels) true")]
        internal static void CloseLeft<T>(SortedSet<T>.Node root, SortedSet<T>.Node pivot, Ghost<SortedSetLabels<T>> labels) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("root == SortedSetOwnership.Top(labels) && SortedSetBalance.CanRotate(false, false, labels)")]
        [Ensures("SortedSetBalance.SingleBefore(root, labels, false)")]
        [PulseBody("SortedSetInductive.Rotation.open_single $(root) $(labels) false")]
        internal static void OpenRight<T>(SortedSet<T>.Node root, Ghost<SortedSetLabels<T>> labels) { }

        [Lemma]
        [Requires("SortedSetBalance.SingleAfter(root, pivot, labels, false)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetBalance.Single(labels, false), Perm.Full)")]
        [Ensures("pivot == SortedSetOwnership.Top(SortedSetBalance.Single(labels, false))")]
        [PulseBody("SortedSetInductive.Rotation.close_single $(root) $(pivot) $(labels) false")]
        internal static void CloseRight<T>(SortedSet<T>.Node root, SortedSet<T>.Node pivot, Ghost<SortedSetLabels<T>> labels) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("root == SortedSetOwnership.Top(labels) && SortedSetBalance.CanRotate(right, right, labels)")]
        [Ensures("SortedSetBalance.SingleBefore(root, labels, right)")]
        [PulseBody("SortedSetInductive.Rotation.open_single $(root) $(labels) $(right)")]
        internal static void OpenSingle<T>(SortedSet<T>.Node root, Ghost<SortedSetLabels<T>> labels, bool right) { }

        [Lemma]
        [Requires("SortedSetBalance.SingleAfter(root, pivot, labels, right)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetBalance.Single(labels, right), Perm.Full)")]
        [Ensures("pivot == SortedSetOwnership.Top(SortedSetBalance.Single(labels, right))")]
        [PulseBody("SortedSetInductive.Rotation.close_single $(root) $(pivot) $(labels) $(right)")]
        internal static void CloseSingle<T>(SortedSet<T>.Node root, SortedSet<T>.Node pivot,
            Ghost<SortedSetLabels<T>> labels, bool right) { }

        [Lemma]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("root == SortedSetOwnership.Top(labels) && SortedSetBalance.CanRotate(right, !right, labels)")]
        [Ensures("SortedSetBalance.DoubleBefore(root, labels, right)")]
        [PulseBody("SortedSetInductive.Rotation.open_double $(root) $(labels) $(right)")]
        internal static void OpenDouble<T>(SortedSet<T>.Node root, Ghost<SortedSetLabels<T>> labels, bool right) { }

        [Lemma]
        [Requires("SortedSetBalance.DoubleAfter(root, pivot, labels, right)")]
        [Ensures("SortedSetOwnership.Owns(SortedSetBalance.Double(labels, right), Perm.Full)")]
        [Ensures("pivot == SortedSetOwnership.Top(SortedSetBalance.Double(labels, right))")]
        [PulseBody("SortedSetInductive.Rotation.close_double $(root) $(pivot) $(labels) $(right)")]
        internal static void CloseDouble<T>(SortedSet<T>.Node root, SortedSet<T>.Node pivot,
            Ghost<SortedSetLabels<T>> labels, bool right) { }
    }
}
#endif
