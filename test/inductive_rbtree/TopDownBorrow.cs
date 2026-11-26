using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveBorrow.fst")]

namespace PalCSharp.Tests.Inductive;

internal static class RbBorrowSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("InductiveBorrow.ready")]
    public static bool Ready<T>(RbLabels<T> n, RbNode<T> current, RbRemovalRotation rotation) => throw Ghost();
    [SpecOp("InductiveBorrow.colored")]
    public static RbLabels<T> Colored<T>(RbLabels<T> n, RbRemovalRotation rotation) => throw Ghost();
    [SpecOp("InductiveBorrow.blackened")]
    public static RbLabels<T> Blackened<T>(RbLabels<T> n, RbRemovalRotation rotation) => throw Ghost();
    [SpecOp("InductiveBorrow.borrowed")]
    public static RbLabels<T> Borrowed<T>(RbLabels<T> n, RbNode<T> current, RbRemovalRotation rotation) => throw Ghost();
    [SpecOp("InductiveBorrow.choose")]
    public static RbRemovalRotation Choose(bool currentLeft, bool siblingLeftRed) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.nred")]
    public static bool Red<T>(RbLabels<T> n) => throw Ghost();
}

internal static class RbBorrowProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveBorrow.left_color $(nodes) $(sibling)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, sibling)")]
    [Ensures("SpecSearchTree.IsRed(RbCursorSpec.Lookup(nodes, RbCursorSpec.Top(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, sibling))))) == RbBorrowSpec.Red(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, sibling)))")]
    public static void LeftColor<T>(RbNode<T> sibling, Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, parent) && root == RbCursorSpec.Top(nodes)")]
    [Requires("grandParent == RbLinkSpec.Parent(nodes, parent) && RbBorrowSpec.Ready(RbLinkSpec.Sub(nodes, parent), current, rotation)")]
    [Ensures("RbCursorSpec.Owns(RbLinkSpec.Replace(nodes, parent, RbBorrowSpec.Borrowed(RbLinkSpec.Sub(nodes, parent), current, rotation)))")]
    [Ensures("Result == RbCursorSpec.Top(RbLinkSpec.Replace(nodes, parent, RbBorrowSpec.Borrowed(RbLinkSpec.Sub(nodes, parent), current, rotation)))")]
    [Ensures("newGrandParent == RbCursorSpec.Top(RbRemoveRotationSpec.Rotate(rotation, RbLinkSpec.Sub(nodes, parent)))")]
    private static RbNode<T>? BorrowAt<T>(RbNode<T>? root, RbNode<T> parent, RbNode<T>? grandParent,
        RbNode<T> current, RbRemovalRotation rotation, out RbNode<T> newGrandParent,
        Ghost<RbLabels<T>> nodes = default)
    {
        RbLinkProof.Cut(parent, nodes);
        RbCursorProof.Facts<T>(RbLinkSpec.Sub(nodes.Value, parent));
        newGrandParent = BorrowLocal(parent, current, rotation);
        return Relink(root, grandParent, parent, newGrandParent);
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, parent) && RbCursorSpec.Member(nodes, sibling)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Result == RbBorrowSpec.Choose(current == RbCursorSpec.Top(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, parent))), RbBorrowSpec.Red(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, sibling))))")]
    private static RbRemovalRotation GetRemovalRotation<T>(RbNode<T> parent, RbNode<T> current,
        RbNode<T> sibling, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Open(parent, nodes);
        bool currentIsLeft = parent.left == current;
        RbCursorProof.Close(parent, nodes);
        RbNode<T>? siblingLeft = LeftAt(sibling);
        bool siblingLeftRed = IsRedAt(siblingLeft);
        RbBorrowProof.LeftColor(sibling, nodes);
        return siblingLeftRed
            ? (currentIsLeft ? RbRemovalRotation.RightLeft : RbRemovalRotation.Right)
            : (currentIsLeft ? RbRemovalRotation.Left : RbRemovalRotation.LeftRight);
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && parent == RbCursorSpec.Top(nodes)")]
    [Requires("RbBorrowSpec.Ready(nodes, current, rotation)")]
    [Ensures("RbCursorSpec.Owns(RbBorrowSpec.Borrowed(nodes, current, rotation))")]
    [Ensures("Result == RbCursorSpec.Top(RbBorrowSpec.Borrowed(nodes, current, rotation))")]
    [Ensures("Result == RbCursorSpec.Top(RbRemoveRotationSpec.Rotate(rotation, nodes))")]
    private static RbNode<T> BorrowLocal<T>(RbNode<T> parent, RbNode<T> current,
        RbRemovalRotation rotation, Ghost<RbLabels<T>> nodes = default)
    {
        RbNode<T> newGrandParent = RotateRemovalLocal(parent, rotation)!;
#if PAL
        Ghost<RbLabels<T>> rotatedModel = RbRemoveRotationSpec.Rotate(rotation, nodes.Value);
        RbCursorProof.Change<T>(RbRemoveRotationSpec.Rotate(rotation, nodes.Value), rotatedModel);
        RbCursorProof.Facts<T>(rotatedModel);
#endif
        bool parentRed = IsRedAt(parent);
        ColorLocal(newGrandParent, parentRed);
#if PAL
        Ghost<RbLabels<T>> coloredModel = RbBorrowSpec.Colored(nodes.Value, rotation);
        RbCursorProof.Change<T>(RbSplitSpec.Color(rotatedModel.Value, parentRed), coloredModel);
        RbCursorProof.Facts<T>(coloredModel);
        RbBalanceProof.TopColor(parent, false, coloredModel);
#endif
        RecolorAt(parent, false);
#if PAL
        Ghost<RbLabels<T>> blackenedModel = RbBorrowSpec.Blackened(nodes.Value, rotation);
        RbCursorProof.Change<T>(RbMutationSpec.Recolor(coloredModel.Value, parent, false), blackenedModel);
        RbCursorProof.Facts<T>(blackenedModel);
        RbBalanceProof.TopColor(current, true, blackenedModel);
#endif
        RecolorAt(current, true);
#if PAL
        RbCursorProof.Change<T>(RbMutationSpec.Recolor(blackenedModel.Value, current, true),
            RbBorrowSpec.Borrowed(nodes.Value, current, rotation));
#endif
        return newGrandParent;
    }
}
