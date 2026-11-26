using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveLocal.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbLocalSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("InductiveLocal.opened")]
    public static SlProp Opened<T>(RbNode<T>? root, RbLabels<T> nodes) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.Tree.left")]
    public static RbLabels<T> Left<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.Tree.right")]
    public static RbLabels<T> Right<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.Tree.Branch?")]
    public static bool Branch<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rot_left")]
    public static RbLabels<T> RotateLeft<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rot_right")]
    public static RbLabels<T> RotateRight<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rot_left_right")]
    public static RbLabels<T> RotateLeftRight<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.SearchTree.rot_right_left")]
    public static RbLabels<T> RotateRightLeft<T>(RbLabels<T> nodes) => throw Ghost();
}

public static class RbLocalProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.left_leaves $(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Right(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Right(nodes)))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Right(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Left(RbLocalSpec.RotateLeft(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Left(RbLocalSpec.RotateLeft(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.RotateLeft(nodes)))")]
    public static void LeftLeaves<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.right_leaves $(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Left(nodes)))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Left(nodes)))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.RotateRight(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Right(RbLocalSpec.RotateRight(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Right(RbLocalSpec.RotateRight(nodes))))")]
    public static void RightLeaves<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.left_right_leaves $(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Left(nodes)) && RbLocalSpec.Branch(RbLocalSpec.Right(RbLocalSpec.Left(nodes)))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Left(nodes)))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Right(RbLocalSpec.Left(nodes))))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Right(RbLocalSpec.Left(nodes))))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Left(RbLocalSpec.RotateLeftRight(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Left(RbLocalSpec.RotateLeftRight(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Right(RbLocalSpec.RotateLeftRight(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Right(RbLocalSpec.RotateLeftRight(nodes))))")]
    public static void LeftRightLeaves<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.right_left_leaves $(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Right(nodes)) && RbLocalSpec.Branch(RbLocalSpec.Left(RbLocalSpec.Right(nodes)))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Left(RbLocalSpec.Right(nodes))))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Left(RbLocalSpec.Right(nodes))))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Right(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Left(RbLocalSpec.RotateRightLeft(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Left(RbLocalSpec.RotateRightLeft(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbLocalSpec.Right(RbLocalSpec.RotateRightLeft(nodes))))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbLocalSpec.Right(RbLocalSpec.RotateRightLeft(nodes))))")]
    public static void RightLeftLeaves<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.open_node $(root) $(nodes)")]
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && root == RbCursorSpec.Top(nodes)")]
    [Ensures("RbLocalSpec.Opened(root, nodes)")]
    [Ensures("root != null")]
    public static void Open<T>(RbNode<T>? root, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLocal.close_node $(root) $(nodes)")]
    [Requires("RbLocalSpec.Opened(root, nodes)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("root == RbCursorSpec.Top(nodes)")]
    public static void Close<T>(RbNode<T>? root, Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    [Requires("RbSpec.Held(node, key, red, left, right)")]
    [Ensures("RbSpec.Held(node, key, red, value, right)")]
    private static void PutLeft<T>(RbNode<T> node, RbNode<T>? value,
        Ghost<T> key = default, Ghost<bool> red = default,
        Ghost<RbNode<T>?> left = default, Ghost<RbNode<T>?> right = default)
    {
        node.left = value;
    }

    [Requires("RbSpec.Held(node, key, red, left, right)")]
    [Ensures("RbSpec.Held(node, key, red, left, value)")]
    private static void PutRight<T>(RbNode<T> node, RbNode<T>? value,
        Ghost<T> key = default, Ghost<bool> red = default,
        Ghost<RbNode<T>?> left = default, Ghost<RbNode<T>?> right = default)
    {
        node.right = value;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("root == RbCursorSpec.Top(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Right(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.RotateLeft(nodes))")]
    [Ensures("Result == RbCursorSpec.Top(RbLocalSpec.RotateLeft(nodes))")]
    public static RbNode<T> RotateLeftLocal<T>(RbNode<T> root, Ghost<RbLabels<T>> nodes = default)
    {
        RbLocalProof.Open(root, nodes);
        RbNode<T>? child = root.right;
        RbLocalProof.Open(child, RbLocalSpec.Right(nodes.Value));
        root.right = child!.left;
        PutLeft(child, root);
        RbLocalProof.LeftLeaves(nodes);
        RbLocalProof.Close(root, RbLocalSpec.Left(RbLocalSpec.RotateLeft(nodes.Value)));
        RbLocalProof.Close(child, RbLocalSpec.RotateLeft(nodes.Value));
        return child;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("root == RbCursorSpec.Top(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Left(nodes))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.RotateRight(nodes))")]
    [Ensures("Result == RbCursorSpec.Top(RbLocalSpec.RotateRight(nodes))")]
    public static RbNode<T> RotateRightLocal<T>(RbNode<T> root, Ghost<RbLabels<T>> nodes = default)
    {
        RbLocalProof.Open(root, nodes);
        RbNode<T>? child = root.left;
        RbLocalProof.Open(child, RbLocalSpec.Left(nodes.Value));
        root.left = child!.right;
        PutRight(child, root);
        RbLocalProof.RightLeaves(nodes);
        RbLocalProof.Close(root, RbLocalSpec.Right(RbLocalSpec.RotateRight(nodes.Value)));
        RbLocalProof.Close(child, RbLocalSpec.RotateRight(nodes.Value));
        return child;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("root == RbCursorSpec.Top(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Left(nodes)) && RbLocalSpec.Branch(RbLocalSpec.Right(RbLocalSpec.Left(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.RotateLeftRight(nodes))")]
    [Ensures("Result == RbCursorSpec.Top(RbLocalSpec.RotateLeftRight(nodes))")]
    public static RbNode<T> RotateLeftRightLocal<T>(RbNode<T> root, Ghost<RbLabels<T>> nodes = default)
    {
        RbLocalProof.Open(root, nodes);
        RbNode<T>? child = root.left;
        RbLocalProof.Open(child, RbLocalSpec.Left(nodes.Value));
        RbNode<T>? grandChild = child!.right;
        RbLocalProof.Open(grandChild, RbLocalSpec.Right(RbLocalSpec.Left(nodes.Value)));
        root.left = grandChild!.right;
        PutRight(grandChild, root);
        PutRight(child, grandChild.left);
        PutLeft(grandChild, child);
        RbLocalProof.LeftRightLeaves(nodes);
        RbLocalProof.Close(root, RbLocalSpec.Right(RbLocalSpec.RotateLeftRight(nodes.Value)));
        RbLocalProof.Close(child, RbLocalSpec.Left(RbLocalSpec.RotateLeftRight(nodes.Value)));
        RbLocalProof.Close(grandChild, RbLocalSpec.RotateLeftRight(nodes.Value));
        return grandChild;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("root == RbCursorSpec.Top(nodes)")]
    [Requires("RbLocalSpec.Branch(nodes) && RbLocalSpec.Branch(RbLocalSpec.Right(nodes)) && RbLocalSpec.Branch(RbLocalSpec.Left(RbLocalSpec.Right(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.RotateRightLeft(nodes))")]
    [Ensures("Result == RbCursorSpec.Top(RbLocalSpec.RotateRightLeft(nodes))")]
    public static RbNode<T> RotateRightLeftLocal<T>(RbNode<T> root, Ghost<RbLabels<T>> nodes = default)
    {
        RbLocalProof.Open(root, nodes);
        RbNode<T>? child = root.right;
        RbLocalProof.Open(child, RbLocalSpec.Right(nodes.Value));
        RbNode<T>? grandChild = child!.left;
        RbLocalProof.Open(grandChild, RbLocalSpec.Left(RbLocalSpec.Right(nodes.Value)));
        root.right = grandChild!.left;
        PutLeft(grandChild, root);
        PutLeft(child, grandChild.right);
        PutRight(grandChild, child);
        RbLocalProof.RightLeftLeaves(nodes);
        RbLocalProof.Close(root, RbLocalSpec.Left(RbLocalSpec.RotateRightLeft(nodes.Value)));
        RbLocalProof.Close(child, RbLocalSpec.Right(RbLocalSpec.RotateRightLeft(nodes.Value)));
        RbLocalProof.Close(grandChild, RbLocalSpec.RotateRightLeft(nodes.Value));
        return grandChild;
    }
}
