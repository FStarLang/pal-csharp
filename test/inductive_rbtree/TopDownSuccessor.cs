using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveSuccessor.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbSuccessorSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("Pulse.Lib.CSharp.TopDownSucc.pre_col")]
    public static RbLabels<T> PreColor<T>(RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveSuccessor.replaced")]
    public static RbLabels<T> Replacement<T>(RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveSuccessor.remaining")]
    public static RbLabels<T> Remaining<T>(RbLabels<T> n) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDownSucc.succ_of")]
    public static RbNode<T>? Successor<T>(RbLabels<T> n) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDownSucc.pos_of")]
    public static RbNode<T>? ParentOfSuccessor<T>(RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveSuccessor.layout")]
    public static bool Layout<T>(RbLabels<T> n, RbNode<T> successor, RbNode<T>? parent) => throw Ghost();
    [SpecOp("InductiveSuccessor.cell")]
    public static SlProp Cell<T>(RbNode<T> node, RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveSuccessor.vacant")]
    public static SlProp Vacant<T>(RbNode<T> node, RbLabels<T> n) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDownSucc.rdel")]
    public static RbLabels<T> Delete<T>(RbLabels<T> n, RbNode<T> match) => throw Ghost();
}

public static class RbSuccessorProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveSuccessor.layout_lemma $(nodes) $(successor) $(parent)")]
    [Requires("RbCursorSpec.Good(nodes) && RbLocalSpec.Branch(nodes)")]
    [Requires("successor == RbSuccessorSpec.Successor(nodes)")]
    [Requires("Pal.Implies(RbLocalSpec.Branch(RbLocalSpec.Right(nodes)), parent == RbSuccessorSpec.ParentOfSuccessor(nodes))")]
    [Ensures("RbSuccessorSpec.Layout(nodes, successor, parent)")]
    public static void Layout<T>(RbNode<T> successor, RbNode<T>? parent, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveSuccessor.empty $(nodes)")]
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("!RbLocalSpec.Branch(nodes)")]
    [Ensures("true")]
    public static void Empty<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveSuccessor.no_right $(nodes)")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(nodes))")]
    [Requires("RbLocalSpec.Branch(nodes) && !RbLocalSpec.Branch(RbLocalSpec.Right(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbSuccessorSpec.PreColor(nodes))")]
    public static void NoRight<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveSuccessor.successor_leaves $(nodes)")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbSuccessorSpec.Remaining(nodes))")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Right(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbSuccessorSpec.PreColor(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbSuccessorSpec.PreColor(nodes)))")]
    public static void Leaves<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveSuccessor.detach $(node) $(nodes)")]
    [Requires("RbSuccessorSpec.Vacant(node, nodes)")]
    [Requires("RbLocalSpec.Branch(nodes)")]
    [Ensures("RbSpec.Detached(node)")]
    public static void Detach<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    [Ensures("Result == node")]
    private static RbNode<T>? NullableNode<T>(RbNode<T> node)
    {
        return node;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbLocalSpec.Branch(nodes) && match == RbCursorSpec.Top(nodes)")]
    [Requires("successor == RbSuccessorSpec.Successor(nodes)")]
    [Requires("Pal.Implies(RbLocalSpec.Branch(RbLocalSpec.Right(nodes)), parentOfSuccessor == RbSuccessorSpec.ParentOfSuccessor(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbSuccessorSpec.Replacement(nodes))")]
    [Ensures("RbSpec.Detached(match)")]
    [Ensures("Result == RbCursorSpec.Top(RbSuccessorSpec.Replacement(nodes))")]
    private static RbNode<T>? ReplaceMatchLocal<T>(RbNode<T> match, RbNode<T> successor,
        RbNode<T>? parentOfSuccessor, Ghost<RbLabels<T>> nodes = default)
    {
        RbSuccessorProof.Layout(successor, parentOfSuccessor, nodes);
        RbLocalProof.Open(match, nodes);
        RbNode<T>? replacement = NullableNode(successor);
        if (successor == match)
        {
            replacement = match.left;
            RbSuccessorProof.NoRight(nodes);
        }
        else
        {
#if PAL
            Ghost<RbLabels<T>> rightModel = RbLocalSpec.Right(nodes.Value);
            Ghost<RbLabels<T>> minimum = RbLinkSpec.Sub(rightModel.Value, successor);
            RbCursorProof.Change<T>(RbLocalSpec.Right(nodes.Value), rightModel);
            RbLinkProof.Cut(successor, rightModel);
            RbCursorProof.Change<T>(RbLinkSpec.Sub(rightModel.Value, successor), minimum);
            RbLocalProof.Open(successor, minimum);
            RbSuccessorProof.Empty<T>(RbLocalSpec.Left(minimum.Value));
            RbCursorProof.Facts<T>(RbLocalSpec.Right(minimum.Value));
#endif
            RbNode<T>? successorRight = successor.right;
            if (successorRight != null)
            {
#if PAL
                RbLocalProof.Open(successorRight, RbLocalSpec.Right(minimum.Value));
#endif
                PutColor(successorRight, false);
#if PAL
                RbSplitProof.BlackLeaves<T>(RbLocalSpec.Right(minimum.Value));
                RbLocalProof.Close(successorRight, RbSplitSpec.Color(RbLocalSpec.Right(minimum.Value), false));
#endif
            }
#if PAL
            else
            {
                RbCursorProof.Change<T>(RbLocalSpec.Right(minimum.Value),
                    RbSplitSpec.Color(RbLocalSpec.Right(minimum.Value), false));
            }
#endif
            if (parentOfSuccessor != match)
            {
#if PAL
                RbLinkProof.OpenParent(successor, parentOfSuccessor!, rightModel);
#endif
                PutLeft(parentOfSuccessor!, successorRight);
#if PAL
                RbLinkProof.CloseParent(successor, parentOfSuccessor!, rightModel,
                    RbSplitSpec.Color(RbLocalSpec.Right(minimum.Value), false));
#endif
                successor.right = match.right;
            }
#if PAL
            else
            {
                RbLinkProof.CloseRoot(successor, rightModel, RbSplitSpec.Color(RbLocalSpec.Right(minimum.Value), false));
            }
            RbCursorProof.Change<T>(
                RbLinkSpec.Replace(rightModel.Value, successor, RbSplitSpec.Color(RbLocalSpec.Right(minimum.Value), false)),
                RbSuccessorSpec.Remaining(nodes.Value));
#endif
            successor.left = match.left;
            RbSuccessorProof.Leaves(nodes);
            RbLocalProof.Close(successor, RbSuccessorSpec.PreColor(nodes.Value));
        }
#if PAL
        Pal.Join(RbCursorSpec.Owns(RbSuccessorSpec.PreColor(nodes.Value)));
        Pal.Join(RbSuccessorSpec.Cell(match, nodes.Value));
        Pal.Join(replacement == RbCursorSpec.Top(RbSuccessorSpec.PreColor(nodes.Value)));
#endif
        if (replacement != null)
        {
            bool color = match.red;
            ColorLocal(replacement, color);
            RbCursorProof.Change<T>(RbSplitSpec.Color(RbSuccessorSpec.PreColor(nodes.Value), color),
                RbSuccessorSpec.Replacement(nodes.Value));
        }
        else
        {
            RbCursorProof.Change<T>(RbSuccessorSpec.PreColor(nodes.Value), RbSuccessorSpec.Replacement(nodes.Value));
        }
        match.left = null;
        match.right = null;
        RbSuccessorProof.Detach(match, nodes);
        return replacement;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, match) && root == RbCursorSpec.Top(nodes)")]
    [Requires("parentOfMatch == RbLinkSpec.Parent(nodes, match)")]
    [Requires("successor == RbSuccessorSpec.Successor(RbLinkSpec.Sub(nodes, match))")]
    [Requires("Pal.Implies(RbLocalSpec.Branch(RbLocalSpec.Right(RbLinkSpec.Sub(nodes, match))), parentOfSuccessor == RbSuccessorSpec.ParentOfSuccessor(RbLinkSpec.Sub(nodes, match)))")]
    [Ensures("RbCursorSpec.Owns(RbSuccessorSpec.Delete(nodes, match))")]
    [Ensures("RbSpec.Detached(match)")]
    [Ensures("Result == RbCursorSpec.Top(RbSuccessorSpec.Delete(nodes, match))")]
    private static RbNode<T>? ReplaceNode<T>(RbNode<T>? root, RbNode<T> match, RbNode<T>? parentOfMatch,
        RbNode<T> successor, RbNode<T>? parentOfSuccessor, Ghost<RbLabels<T>> nodes = default)
    {
        RbLinkProof.Cut(match, nodes);
        RbCursorProof.Facts<T>(RbLinkSpec.Sub(nodes.Value, match));
        RbNode<T>? replacement = ReplaceMatchLocal(match, successor, parentOfSuccessor);
        RbNode<T>? result = Relink(root, parentOfMatch, match, replacement);
        RbCursorProof.Change<T>(
            RbLinkSpec.Replace(nodes.Value, match, RbSuccessorSpec.Replacement(RbLinkSpec.Sub(nodes.Value, match))),
            RbSuccessorSpec.Delete(nodes.Value, match));
        return result;
    }
}
