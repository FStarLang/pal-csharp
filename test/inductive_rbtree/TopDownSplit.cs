using System;
using System.Diagnostics;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static class RbSplitSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("Pulse.Lib.CSharp.TopDown.recolorn")]
    public static RbLabels<T> Color<T>(RbLabels<T> n, bool red) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.split4n")]
    public static RbLabels<T> Split<T>(RbLabels<T> n) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.is4")]
    public static bool Is4<T>(RbLabels<T> n) => throw Ghost();
}

public static class RbSplitProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.black_leaves $(nodes)")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(nodes))")]
    [Requires("RbLocalSpec.Branch(nodes)")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbSplitSpec.Color(nodes, false)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbSplitSpec.Color(nodes, false)))")]
    public static void BlackLeaves<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.color_leaves $(nodes) $(red)")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(nodes))")]
    [Requires("RbLocalSpec.Branch(nodes)")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbSplitSpec.Color(nodes, red)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbSplitSpec.Color(nodes, red)))")]
    public static void ColorLeaves<T>(bool red, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.split_leaves $(nodes)")]
    [Requires("RbCursorSpec.Owns(RbSplitSpec.Color(RbLocalSpec.Left(nodes), false))")]
    [Requires("RbCursorSpec.Owns(RbSplitSpec.Color(RbLocalSpec.Right(nodes), false))")]
    [Requires("RbLocalSpec.Branch(nodes)")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbSplitSpec.Split(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbSplitSpec.Split(nodes)))")]
    public static void SplitLeaves<T>(Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    [Requires("RbSpec.Held(node, key, red, left, right)")]
    [Ensures("RbSpec.Held(node, key, value, left, right)")]
    private static void PutColor<T>(RbNode<T> node, bool value,
        Ghost<T> key = default, Ghost<bool> red = default,
        Ghost<RbNode<T>?> left = default, Ghost<RbNode<T>?> right = default)
    {
        node.red = value;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && (node == null || RbCursorSpec.Member(nodes, node))")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Result == SpecSearchTree.IsRed(RbCursorSpec.Lookup(nodes, node))")]
    public static bool IsRedAt<T>(RbNode<T>? node, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Root(nodes);
        if (node == null)
            return false;
        RbCursorProof.Open(node, nodes);
        bool result = node.red;
        RbCursorProof.Close(node, nodes);
        return result;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, node)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("Result == RbSplitSpec.Is4(RbLinkSpec.Sub(nodes, node))")]
    public static bool Is4At<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Open(node, nodes);
        RbNode<T>? left = node.left;
        RbCursorProof.Close(node, nodes);
        if (!IsRedAt(left))
            return false;
        RbCursorProof.Open(node, nodes);
        RbNode<T>? right = node.right;
        RbCursorProof.Close(node, nodes);
        return IsRedAt(right);
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && root == RbCursorSpec.Top(nodes)")]
    [Ensures("RbCursorSpec.Owns(RbSplitSpec.Color(nodes, red))")]
    public static void ColorLocal<T>(RbNode<T> root, bool red, Ghost<RbLabels<T>> nodes = default)
    {
        RbLocalProof.Open(root, nodes);
        root.red = red;
        RbSplitProof.ColorLeaves(red, nodes);
        RbLocalProof.Close(root, RbSplitSpec.Color(nodes.Value, red));
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("root == RbCursorSpec.Top(nodes) && RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Left(nodes)) && RbLocalSpec.Branch(RbLocalSpec.Right(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbSplitSpec.Split(nodes))")]
    public static void Split4Local<T>(RbNode<T> root, Ghost<RbLabels<T>> nodes = default)
    {
        RbLocalProof.Open(root, nodes);
        root.red = true;
        RbNode<T> left = root.left!;
        RbLocalProof.Open(left, RbLocalSpec.Left(nodes.Value));
        PutColor(left, false);
        RbSplitProof.BlackLeaves<T>(RbLocalSpec.Left(nodes.Value));
        RbLocalProof.Close(left, RbSplitSpec.Color(RbLocalSpec.Left(nodes.Value), false));
        RbNode<T> right = root.right!;
        RbLocalProof.Open(right, RbLocalSpec.Right(nodes.Value));
        PutColor(right, false);
        RbSplitProof.BlackLeaves<T>(RbLocalSpec.Right(nodes.Value));
        RbLocalProof.Close(right, RbSplitSpec.Color(RbLocalSpec.Right(nodes.Value), false));
        RbSplitProof.SplitLeaves(nodes);
        RbLocalProof.Close(root, RbSplitSpec.Split(nodes.Value));
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, node)")]
    [Requires("RbSplitSpec.Is4(RbLinkSpec.Sub(nodes, node))")]
    [Ensures("RbCursorSpec.Owns(RbLinkSpec.Replace(nodes, node, RbSplitSpec.Split(RbLinkSpec.Sub(nodes, node))))")]
    public static void Split4At<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes = default)
    {
        RbLinkProof.Cut(node, nodes);
        Split4Local(node);
        RbLinkProof.JoinSame(node, nodes, RbSplitSpec.Split(RbLinkSpec.Sub(nodes.Value, node)));
    }
}
