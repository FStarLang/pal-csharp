using System;
using System.Collections.Generic;
using System.Diagnostics;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static class RbRemoveLocalSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("Pulse.Lib.CSharp.TopDownRemove.is2")]
    public static bool Is2<T>(RbLabels<T> n) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.merge2n")]
    public static RbLabels<T> Merge<T>(RbLabels<T> n) => throw Ghost();
}

public static class RbRemoveLocalProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.red_leaves $(nodes)")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(nodes))")]
    [Requires("RbLocalSpec.Branch(nodes)")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbSplitSpec.Color(nodes, true)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbSplitSpec.Color(nodes, true)))")]
    public static void RedLeaves<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.merge_leaves $(nodes)")]
    [Requires("RbCursorSpec.Owns(RbSplitSpec.Color(RbLocalSpec.Left(nodes), true))")]
    [Requires("RbCursorSpec.Owns(RbSplitSpec.Color(RbLocalSpec.Right(nodes), true))")]
    [Requires("RbLocalSpec.Branch(nodes)")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbRemoveLocalSpec.Merge(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbRemoveLocalSpec.Merge(nodes)))")]
    public static void MergeLeaves<T>(Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, current)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Result == RbRemoveSpec.Order(comparer, key, nodes, current, found)")]
    private static int RemovalOrder<T>(RbNode<T> current, T key, IComparer<T> comparer,
        bool found, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Open(current, nodes);
        int order = found ? -1 : comparer.Compare(key, current.key);
        RbCursorProof.Close(current, nodes);
        return order;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, node)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Result == RbCursorSpec.Top(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, node)))")]
    [Ensures("Result == null || RbCursorSpec.Member(nodes, Result)")]
    private static RbNode<T>? LeftAt<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Open(node, nodes);
        RbNode<T>? result = node.left;
        RbCursorProof.Close(node, nodes);
        return result;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, node)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Result == RbCursorSpec.Top(RbLocalSpec.Right(RbLinkSpec.Sub(nodes, node)))")]
    [Ensures("Result == null || RbCursorSpec.Member(nodes, Result)")]
    private static RbNode<T>? RightAt<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Open(node, nodes);
        RbNode<T>? result = node.right;
        RbCursorProof.Close(node, nodes);
        return result;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, node)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Result == RbRemoveLocalSpec.Is2(RbLinkSpec.Sub(nodes, node))")]
    private static bool Is2At<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Open(node, nodes);
        bool red = node.red;
        RbCursorProof.Close(node, nodes);
        if (red)
            return false;
        RbNode<T>? left = LeftAt(node);
        if (IsRedAt(left))
            return false;
        RbNode<T>? right = RightAt(node);
        return !IsRedAt(right);
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, parent)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Pal.Implies(current == RbCursorSpec.Top(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, parent))), Result == RbCursorSpec.Top(RbLocalSpec.Right(RbLinkSpec.Sub(nodes, parent))))")]
    [Ensures("Pal.Implies(current != RbCursorSpec.Top(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, parent))), Result == RbCursorSpec.Top(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, parent))))")]
    [Ensures("Result == null || RbCursorSpec.Member(nodes, Result)")]
    private static RbNode<T>? SiblingAt<T>(RbNode<T> parent, RbNode<T> current, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Open(parent, nodes);
        RbNode<T>? result = current == parent.left ? parent.right : parent.left;
        RbCursorProof.Close(parent, nodes);
        return result;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("root == RbCursorSpec.Top(nodes) && RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Left(nodes)) && RbLocalSpec.Branch(RbLocalSpec.Right(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbRemoveLocalSpec.Merge(nodes))")]
    private static void Merge2Local<T>(RbNode<T> root, Ghost<RbLabels<T>> nodes = default)
    {
        RbLocalProof.Open(root, nodes);
        root.red = false;
        RbNode<T> left = root.left!;
        RbLocalProof.Open(left, RbLocalSpec.Left(nodes.Value));
        PutColor(left, true);
        RbRemoveLocalProof.RedLeaves<T>(RbLocalSpec.Left(nodes.Value));
        RbLocalProof.Close(left, RbSplitSpec.Color(RbLocalSpec.Left(nodes.Value), true));
        RbNode<T> right = root.right!;
        RbLocalProof.Open(right, RbLocalSpec.Right(nodes.Value));
        PutColor(right, true);
        RbRemoveLocalProof.RedLeaves<T>(RbLocalSpec.Right(nodes.Value));
        RbLocalProof.Close(right, RbSplitSpec.Color(RbLocalSpec.Right(nodes.Value), true));
        RbRemoveLocalProof.MergeLeaves(nodes);
        RbLocalProof.Close(root, RbRemoveLocalSpec.Merge(nodes.Value));
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, node)")]
    [Requires("RbLocalSpec.Branch(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, node))) && RbLocalSpec.Branch(RbLocalSpec.Right(RbLinkSpec.Sub(nodes, node)))")]
    [Ensures("RbCursorSpec.Owns(RbLinkSpec.Replace(nodes, node, RbRemoveLocalSpec.Merge(RbLinkSpec.Sub(nodes, node))))")]
    private static void Merge2At<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes = default)
    {
        RbLinkProof.Cut(node, nodes);
        Merge2Local(node);
        RbLinkProof.JoinSame(node, nodes, RbRemoveLocalSpec.Merge(RbLinkSpec.Sub(nodes.Value, node)));
    }
}
