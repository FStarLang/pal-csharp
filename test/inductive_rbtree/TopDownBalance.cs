using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveBalance.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbBalanceSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("Pulse.Lib.CSharp.TopDown.balance_ready")]
    public static bool Ready<T>(RbLabels<T> n, RbNode<T> cur, RbNode<T>? par, RbNode<T> gp, RbNode<T>? ggp) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.balance")]
    public static RbLabels<T> Balanced<T>(RbLabels<T> n, RbNode<T> cur) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.balance_sub")]
    public static RbLabels<T> SubBalanced<T>(bool currentRight, bool parentRight, RbLabels<T> n) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.rot_for")]
    public static RbLabels<T> Rotated<T>(bool currentRight, bool parentRight, RbLabels<T> n) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.same_side")]
    public static bool SameSide<T>(RbLabels<T> n, RbNode<T> cur) => throw Ghost();
    [SpecOp("InductiveBalance.current_right")]
    public static bool CurrentRight<T>(RbLabels<T> n, RbNode<T> cur, RbNode<T>? par) => throw Ghost();
    [SpecOp("InductiveBalance.parent_right")]
    public static bool ParentRight<T>(RbLabels<T> n, RbNode<T>? par, RbNode<T> gp) => throw Ghost();
    [SpecOp("InductiveBalance.can_rotate")]
    public static bool CanRotate<T>(bool currentRight, bool parentRight, RbLabels<T> n) => throw Ghost();
}

public static class RbBalanceProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveBalance.layout $(nodes) $(current) $(parent) $(grandParent) $(greatGrandParent)")]
    [Requires("RbBalanceSpec.Ready(nodes, current, parent, grandParent, greatGrandParent)")]
    [Ensures("RbCursorSpec.Good(nodes)")]
    [Ensures("RbCursorSpec.Member(nodes, parent) && RbCursorSpec.Member(nodes, grandParent)")]
    [Ensures("parent != null")]
    [Ensures("RbLinkSpec.Parent(nodes, grandParent) == greatGrandParent")]
    [Ensures("RbCursorSpec.Good(RbLinkSpec.Sub(nodes, grandParent))")]
    [Ensures("RbBalanceSpec.CanRotate(RbBalanceSpec.CurrentRight(nodes, current, parent), RbBalanceSpec.ParentRight(nodes, parent, grandParent), RbLinkSpec.Sub(nodes, grandParent))")]
    [Ensures("RbBalanceSpec.SameSide(nodes, current) == (RbBalanceSpec.CurrentRight(nodes, current, parent) == RbBalanceSpec.ParentRight(nodes, parent, grandParent))")]
    [Ensures("RbCursorSpec.Same(RbBalanceSpec.Balanced(nodes, current), RbLinkSpec.Replace(nodes, grandParent, RbBalanceSpec.SubBalanced(RbBalanceSpec.CurrentRight(nodes, current, parent), RbBalanceSpec.ParentRight(nodes, parent, grandParent), RbLinkSpec.Sub(nodes, grandParent))))")]
    public static void Layout<T>(RbNode<T> current, RbNode<T>? parent, RbNode<T> grandParent,
        RbNode<T>? greatGrandParent, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveBalance.rotated_facts $(nodes) $(currentRight) $(parentRight)")]
    [Requires("RbCursorSpec.Good(nodes) && RbBalanceSpec.CanRotate(currentRight, parentRight, nodes)")]
    [Ensures("RbCursorSpec.Member(RbBalanceSpec.Rotated(currentRight, parentRight, nodes), RbCursorSpec.Top(nodes))")]
    public static void RotatedFacts<T>(bool currentRight, bool parentRight, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveBalance.top_color $(nodes) $(node) $(red)")]
    [Requires("RbCursorSpec.Good(nodes) && (node == null || RbCursorSpec.Member(nodes, node))")]
    [Ensures("RbCursorSpec.Top(RbMutationSpec.Recolor(nodes, node, red)) == RbCursorSpec.Top(nodes)")]
    public static void TopColor<T>(RbNode<T>? node, bool red, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveBalance.balance_result $(nodes) $(currentRight) $(parentRight)")]
    [Requires("RbCursorSpec.Top(nodes) != null")]
    [Requires("RbCursorSpec.Good(RbMutationSpec.Recolor(RbBalanceSpec.Rotated(currentRight, parentRight, nodes), RbCursorSpec.Top(nodes), true))")]
    [Ensures("RbCursorSpec.Same(RbMutationSpec.Recolor(RbMutationSpec.Recolor(RbBalanceSpec.Rotated(currentRight, parentRight, nodes), RbCursorSpec.Top(nodes), true), RbCursorSpec.Top(RbMutationSpec.Recolor(RbBalanceSpec.Rotated(currentRight, parentRight, nodes), RbCursorSpec.Top(nodes), true)), false), RbBalanceSpec.SubBalanced(currentRight, parentRight, nodes))")]
    public static void Result<T>(bool currentRight, bool parentRight, Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("root == RbCursorSpec.Top(nodes)")]
    [Requires("RbBalanceSpec.Ready(nodes, current, parent, grandParent, greatGrandParent)")]
    [Ensures("RbCursorSpec.Owns(RbBalanceSpec.Balanced(nodes, current))")]
    [Ensures("Result == RbCursorSpec.Top(RbBalanceSpec.Balanced(nodes, current))")]
    [Ensures("parent == (RbBalanceSpec.SameSide(nodes, current) ? Pal.Old(parent) : greatGrandParent)")]
    public static RbNode<T>? InsertionBalance<T>(RbNode<T>? root, RbNode<T> current,
        ref RbNode<T>? parent, RbNode<T> grandParent, RbNode<T>? greatGrandParent,
        Ghost<RbLabels<T>> nodes = default)
    {
        RbBalanceProof.Layout(current, parent, grandParent, greatGrandParent, nodes);
        RbCursorProof.Open(grandParent, nodes);
        bool parentIsOnRight = grandParent.right == parent;
        RbCursorProof.Close(grandParent, nodes);
        RbNode<T> parentNode = parent!;
        RbCursorProof.Open(parentNode, nodes);
        bool currentIsOnRight = parentNode.right == current;
        RbCursorProof.Close(parentNode, nodes);
#if PAL
        Ghost<RbLabels<T>> sub = RbLinkSpec.Sub(nodes.Value, grandParent);
        Ghost<RbLabels<T>> rotatedModel = RbBalanceSpec.Rotated(currentIsOnRight, parentIsOnRight, sub.Value);
#endif
        RbLinkProof.Cut(grandParent, nodes);
        RbNode<T> newChild = grandParent;
        if (parentIsOnRight == currentIsOnRight)
        {
            if (currentIsOnRight)
            {
                newChild = RotateLeftLocal(grandParent);
#if PAL
                RbCursorProof.Change<T>(RbLocalSpec.RotateLeft(RbLinkSpec.Sub(nodes.Value, grandParent)),
                    rotatedModel);
#endif
            }
            else
            {
                newChild = RotateRightLocal(grandParent);
#if PAL
                RbCursorProof.Change<T>(RbLocalSpec.RotateRight(RbLinkSpec.Sub(nodes.Value, grandParent)),
                    rotatedModel);
#endif
            }
#if PAL
            Pal.Join(newChild == RbCursorSpec.Top(rotatedModel.Value));
            Pal.Join(RbCursorSpec.Owns(rotatedModel.Value));
            Pal.Join(RbLinkSpec.Pending(nodes.Value, grandParent));
#endif
        }
        else
        {
            if (currentIsOnRight)
            {
                newChild = RotateLeftRightLocal(grandParent);
#if PAL
                RbCursorProof.Change<T>(RbLocalSpec.RotateLeftRight(RbLinkSpec.Sub(nodes.Value, grandParent)),
                    rotatedModel);
#endif
            }
            else
            {
                newChild = RotateRightLeftLocal(grandParent);
#if PAL
                RbCursorProof.Change<T>(RbLocalSpec.RotateRightLeft(RbLinkSpec.Sub(nodes.Value, grandParent)),
                    rotatedModel);
#endif
            }
#if PAL
            Pal.Join(newChild == RbCursorSpec.Top(rotatedModel.Value));
            Pal.Join(RbCursorSpec.Owns(rotatedModel.Value));
            Pal.Join(RbLinkSpec.Pending(nodes.Value, grandParent));
#endif
            parent = greatGrandParent;
        }
#if PAL
        Pal.Join(newChild == RbCursorSpec.Top(rotatedModel.Value));
        Pal.Join(parent == (RbBalanceSpec.SameSide(nodes.Value, current) ? parentNode : greatGrandParent));
        Pal.Join(RbCursorSpec.Owns(rotatedModel.Value));
        Pal.Join(RbLinkSpec.Pending(nodes.Value, grandParent));
        RbCursorProof.Facts<T>(rotatedModel);
        RbBalanceProof.RotatedFacts(currentIsOnRight, parentIsOnRight, sub);
        RbBalanceProof.TopColor(grandParent, true, rotatedModel);
        Ghost<RbLabels<T>> redModel = RbMutationSpec.Recolor(rotatedModel.Value, grandParent, true);
#endif
        RecolorAt(grandParent, true);
#if PAL
        RbCursorProof.Change<T>(RbMutationSpec.Recolor(rotatedModel.Value, grandParent, true), redModel);
        RbCursorProof.Facts<T>(redModel);
        RbCursorProof.Root<T>(redModel);
#endif
        RecolorAt(newChild, false);
#if PAL
        RbBalanceProof.Result(currentIsOnRight, parentIsOnRight, sub);
        RbCursorProof.Change<T>(RbMutationSpec.Recolor(redModel.Value, newChild, false),
            RbBalanceSpec.SubBalanced(currentIsOnRight, parentIsOnRight, sub.Value));
#endif
        RbNode<T>? result = Relink(root, greatGrandParent, grandParent, newChild);
#if PAL
        RbCursorProof.Change<T>(
            RbLinkSpec.Replace(nodes.Value, grandParent,
                RbBalanceSpec.SubBalanced(currentIsOnRight, parentIsOnRight, sub.Value)),
            RbBalanceSpec.Balanced(nodes.Value, current));
#endif
        return result;
    }
}
