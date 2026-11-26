using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveLift.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbLiftSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("InductiveLift.child")]
    public static bool Child<T>(RbLabels<T> n, RbNode<T> child) => throw Ghost();
    [SpecOp("InductiveLift.right")]
    public static bool Right<T>(RbLabels<T> n, RbNode<T> child) => throw Ghost();
    [SpecOp("InductiveLift.rotated")]
    public static RbLabels<T> Rotated<T>(RbLabels<T> n, RbNode<T> child) => throw Ghost();
    [SpecOp("InductiveLift.lifted")]
    public static RbLabels<T> Lifted<T>(RbLabels<T> n, RbNode<T> child) => throw Ghost();
    [SpecOp("InductiveLift.whole")]
    public static RbLabels<T> Whole<T>(RbLabels<T> n, RbNode<T> parent, RbNode<T> child) => throw Ghost();
}

public static class RbLiftProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLift.layout $(nodes) $(sibling)")]
    [Requires("RbCursorSpec.Good(nodes) && RbLiftSpec.Child(nodes, sibling)")]
    [Ensures("RbLiftSpec.Right(nodes, sibling) ? RbLocalSpec.Branch(RbLocalSpec.Right(nodes)) : RbLocalSpec.Branch(RbLocalSpec.Left(nodes))")]
    [Ensures("RbCursorSpec.Top(RbLiftSpec.Rotated(nodes, sibling)) == sibling")]
    [Ensures("RbCursorSpec.Member(RbLiftSpec.Rotated(nodes, sibling), RbCursorSpec.Top(nodes))")]
    public static void Layout<T>(RbNode<T> sibling, Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && root == RbCursorSpec.Top(nodes) && RbCursorSpec.Member(nodes, parent)")]
    [Requires("grandParent == RbLinkSpec.Parent(nodes, parent)")]
    [Requires("RbLiftSpec.Child(RbLinkSpec.Sub(nodes, parent), sibling)")]
    [Ensures("RbCursorSpec.Owns(RbLiftSpec.Whole(nodes, parent, sibling))")]
    [Ensures("Result == RbCursorSpec.Top(RbLiftSpec.Whole(nodes, parent, sibling))")]
    private static RbNode<T>? LiftSibling<T>(RbNode<T>? root, RbNode<T> parent,
        RbNode<T>? grandParent, RbNode<T> sibling, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Open(parent, nodes);
        bool siblingRight = parent.right == sibling;
        RbCursorProof.Close(parent, nodes);
        RbLinkProof.Cut(parent, nodes);
#if PAL
        Ghost<RbLabels<T>> subtree = RbLinkSpec.Sub(nodes.Value, parent);
        Ghost<RbLabels<T>> rotatedModel = RbLiftSpec.Rotated(subtree.Value, sibling);
        RbCursorProof.Change<T>(RbLinkSpec.Sub(nodes.Value, parent), subtree);
        RbCursorProof.Facts<T>(subtree);
        RbLiftProof.Layout(sibling, subtree);
#endif
        if (siblingRight)
        {
            RbNode<T> ignored = RotateLeftLocal(parent);
#if PAL
            RbCursorProof.Change<T>(RbLocalSpec.RotateLeft(subtree.Value), rotatedModel);
#endif
        }
        else
        {
            RbNode<T> ignored = RotateRightLocal(parent);
#if PAL
            RbCursorProof.Change<T>(RbLocalSpec.RotateRight(subtree.Value), rotatedModel);
#endif
        }
#if PAL
        Pal.Join(RbCursorSpec.Owns(rotatedModel.Value));
        Pal.Join(RbLinkSpec.Pending(nodes.Value, parent));
        RbCursorProof.Facts<T>(rotatedModel);
        RbBalanceProof.TopColor(parent, true, rotatedModel);
        Ghost<RbLabels<T>> redModel = RbMutationSpec.Recolor(rotatedModel.Value, parent, true);
#endif
        RecolorAt(parent, true);
#if PAL
        RbCursorProof.Change<T>(RbMutationSpec.Recolor(rotatedModel.Value, parent, true), redModel);
#endif
        ColorLocal(sibling, false);
#if PAL
        RbCursorProof.Change<T>(RbSplitSpec.Color(redModel.Value, false), RbLiftSpec.Lifted(subtree.Value, sibling));
#endif
        RbNode<T>? result = Relink(root, grandParent, parent, sibling);
#if PAL
        RbCursorProof.Change<T>(
            RbLinkSpec.Replace(nodes.Value, parent, RbLiftSpec.Lifted(subtree.Value, sibling)),
            RbLiftSpec.Whole(nodes.Value, parent, sibling));
#endif
        return result;
    }
}
