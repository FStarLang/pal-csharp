using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveRelink.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbLinkSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("Pulse.Lib.CSharp.RegionPath.sub")]
    public static RbLabels<T> Sub<T>(RbLabels<T> nodes, RbNode<T>? node) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.RegionPath.replace")]
    public static RbLabels<T> Replace<T>(RbLabels<T> nodes, RbNode<T>? node, RbLabels<T> replacement) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.parent_of")]
    public static RbNode<T>? Parent<T>(RbLabels<T> nodes, RbNode<T>? node) => throw Ghost();
    [SpecOp("InductiveRelink.pending")]
    public static SlProp Pending<T>(RbLabels<T> nodes, RbNode<T>? node) => throw Ghost();
    [SpecOp("InductiveRelink.cell")]
    public static SlProp Cell<T>(RbLabels<T> nodes, RbNode<T>? node, RbNode<T>? parent, RbNode<T>? hole) => throw Ghost();
}

public static class RbLinkProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRelink.join_same $(nodes) $(node) $(replacement)")]
    [Requires("RbLinkSpec.Pending(nodes, node)")]
    [Requires("RbCursorSpec.Owns(replacement)")]
    [Requires("RbCursorSpec.Top(replacement) == node")]
    [Ensures("RbCursorSpec.Owns(RbLinkSpec.Replace(nodes, node, replacement))")]
    public static void JoinSame<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes, Ghost<RbLabels<T>> replacement) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRelink.cut $(nodes) $(node)")]
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Member(nodes, node)")]
    [Ensures("RbCursorSpec.Owns(RbLinkSpec.Sub(nodes, node))")]
    [Ensures("RbLinkSpec.Pending(nodes, node)")]
    public static void Cut<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRelink.open_parent $(nodes) $(node) $(parent)")]
    [Requires("RbLinkSpec.Pending(nodes, node)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, node)")]
    [Requires("parent == RbLinkSpec.Parent(nodes, node)")]
    [Ensures("RbLinkSpec.Cell(nodes, node, parent, node)")]
    public static void OpenParent<T>(RbNode<T> node, RbNode<T> parent, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRelink.close_parent $(nodes) $(node) $(parent) $(replacement)")]
    [Requires("RbLinkSpec.Cell(nodes, node, parent, RbCursorSpec.Top(replacement))")]
    [Requires("RbCursorSpec.Owns(replacement)")]
    [Ensures("RbCursorSpec.Owns(RbLinkSpec.Replace(nodes, node, replacement))")]
    [Ensures("RbCursorSpec.Top(RbLinkSpec.Replace(nodes, node, replacement)) == RbCursorSpec.Top(nodes)")]
    public static void CloseParent<T>(RbNode<T> node, RbNode<T> parent,
        Ghost<RbLabels<T>> nodes, Ghost<RbLabels<T>> replacement) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRelink.close_root $(nodes) $(node) $(replacement)")]
    [Requires("RbLinkSpec.Pending(nodes, node)")]
    [Requires("RbCursorSpec.Owns(replacement)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, node)")]
    [Requires("RbLinkSpec.Parent(nodes, node) == null")]
    [Ensures("RbCursorSpec.Owns(RbLinkSpec.Replace(nodes, node, replacement))")]
    [Ensures("RbCursorSpec.Top(RbLinkSpec.Replace(nodes, node, replacement)) == RbCursorSpec.Top(replacement)")]
    public static void CloseRoot<T>(RbNode<T> node, Ghost<RbLabels<T>> nodes,
        Ghost<RbLabels<T>> replacement) { }
}

public static partial class RbTree
{
    // The subtree has already been transformed. The pending spine owns every
    // ancestor and off-path sibling; this is the one real parent-link write.
    [Requires("RbLinkSpec.Pending(nodes, child)")]
    [Requires("RbCursorSpec.Owns(replacement)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, child)")]
    [Requires("root == RbCursorSpec.Top(nodes)")]
    [Requires("parent == RbLinkSpec.Parent(nodes, child)")]
    [Requires("newChild == RbCursorSpec.Top(replacement)")]
    [Ensures("RbCursorSpec.Owns(RbLinkSpec.Replace(nodes, child, replacement))")]
    [Ensures("Result == RbCursorSpec.Top(RbLinkSpec.Replace(nodes, child, replacement))")]
    public static RbNode<T>? Relink<T>(RbNode<T>? root, RbNode<T>? parent,
        RbNode<T> child, RbNode<T>? newChild,
        Ghost<RbLabels<T>> nodes = default, Ghost<RbLabels<T>> replacement = default)
    {
        if (parent != null)
        {
            RbLinkProof.OpenParent(child, parent, nodes);
            if (parent.left == child)
                parent.left = newChild;
            else
                parent.right = newChild;
            RbLinkProof.CloseParent(child, parent, nodes, replacement);
            return root;
        }
        else
        {
            RbLinkProof.CloseRoot(child, nodes, replacement);
            return newChild;
        }
    }
}
