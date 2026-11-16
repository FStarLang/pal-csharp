using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveLeaf.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbLeafSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("Pulse.Lib.CSharp.TopDown.leaf")]
    public static RbLabels<T> Leaf<T>(RbNode<T> node, T key) => throw Ghost();
    [SpecOp("InductiveLeaf.attach")]
    public static RbLabels<T> Attach<T>(RbLabels<T> n, RbLabels<T> child, bool right) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.set_child")]
    public static RbLabels<T> SetChild<T>(RbLabels<T> n, RbNode<T> parent, bool right, RbLabels<T> child) => throw Ghost();
}

public static class RbLeafProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLeaf.make_leaf $(node) $(key) $(red)")]
    [Requires("RbSpec.Held(node, key, red, null, null)")]
    [Ensures("RbCursorSpec.Owns(RbSplitSpec.Color(RbLeafSpec.Leaf(node, key), red))")]
    [Ensures("node != null")]
    public static void Make<T>(RbNode<T> node, T key, bool red) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLeaf.fresh $(nodes) $(node) $(key)")]
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Owns(RbLeafSpec.Leaf(node, key))")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    [Ensures("RbCursorSpec.Owns(RbLeafSpec.Leaf(node, key))")]
    [Ensures("!RbCursorSpec.Member(nodes, node)")]
    public static void Fresh<T>(RbNode<T> node, T key, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveLeaf.attach_leaves $(nodes) $(child) $(right)")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Left(nodes))")]
    [Requires("RbCursorSpec.Owns(RbLocalSpec.Right(nodes))")]
    [Requires("RbCursorSpec.Owns(child)")]
    [Requires("RbLocalSpec.Branch(nodes) && !(right ? RbLocalSpec.Branch(RbLocalSpec.Right(nodes)) : RbLocalSpec.Branch(RbLocalSpec.Left(nodes)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Left(RbLeafSpec.Attach(nodes, child, right)))")]
    [Ensures("RbCursorSpec.Owns(RbLocalSpec.Right(RbLeafSpec.Attach(nodes, child, right)))")]
    public static void AttachLeaves<T>(bool right, Ghost<RbLabels<T>> nodes, Ghost<RbLabels<T>> child) { }
}

public static partial class RbTree
{
    [Ensures("RbCursorSpec.Owns(RbSplitSpec.Color(RbLeafSpec.Leaf(Result, key), red))")]
    public static RbNode<T> NewLeaf<T>(T key, bool red)
    {
        RbNode<T> node = new RbNode<T> { key = key, red = red, left = null, right = null };
        RbLeafProof.Make(node, key, red);
        return node;
    }

    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Owns(RbLeafSpec.Leaf(node, key))")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, parent)")]
    [Requires("!(right ? RbLocalSpec.Branch(RbLocalSpec.Right(RbLinkSpec.Sub(nodes, parent))) : RbLocalSpec.Branch(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, parent))))")]
    [Ensures("RbCursorSpec.Owns(RbLeafSpec.SetChild(nodes, parent, right, RbLeafSpec.Leaf(node, key)))")]
    public static void LinkLeaf<T>(RbNode<T> parent, RbNode<T> node, bool right, T key,
        Ghost<RbLabels<T>> nodes = default)
    {
        RbLinkProof.Cut(parent, nodes);
        RbLocalProof.Open(parent, RbLinkSpec.Sub(nodes.Value, parent));
        if (right)
            parent.right = node;
        else
            parent.left = node;
        RbLeafProof.AttachLeaves<T>(right, RbLinkSpec.Sub(nodes.Value, parent), RbLeafSpec.Leaf(node, key));
        RbLocalProof.Close(parent, RbLeafSpec.Attach(RbLinkSpec.Sub(nodes.Value, parent), RbLeafSpec.Leaf(node, key), right));
        RbLinkProof.JoinSame(parent, nodes, RbLeafSpec.Attach(RbLinkSpec.Sub(nodes.Value, parent), RbLeafSpec.Leaf(node, key), right));
        RbCursorProof.Change<T>(
            RbLinkSpec.Replace(nodes.Value, parent, RbLeafSpec.Attach(RbLinkSpec.Sub(nodes.Value, parent), RbLeafSpec.Leaf(node, key), right)),
            RbLeafSpec.SetChild(nodes.Value, parent, right, RbLeafSpec.Leaf(node, key)));
    }
}
