using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveRemoveRotation.fst")]

namespace PalCSharp.Tests.Inductive;

[SpecType("Pulse.Lib.CSharp.SearchTree.tree_rotation")]
internal enum RbRemovalRotation : byte
{
    [SpecCase("Pulse.Lib.CSharp.SearchTree.RotLeft")] Left,
    [SpecCase("Pulse.Lib.CSharp.SearchTree.RotLeftRight")] LeftRight,
    [SpecCase("Pulse.Lib.CSharp.SearchTree.RotRight")] Right,
    [SpecCase("Pulse.Lib.CSharp.SearchTree.RotRightLeft")] RightLeft
}

internal static class RbRemoveRotationSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("Pulse.Lib.CSharp.TopDownRemove.rotn")]
    public static RbLabels<T> Rotate<T>(RbRemovalRotation rotation, RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveRemoveRotation.can_rotate")]
    public static bool CanRotate<T>(RbRemovalRotation rotation, RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveRemoveRotation.prepared")]
    public static RbLabels<T> Prepared<T>(RbLabels<T> n, bool right) => throw Ghost();
    [SpecOp("InductiveRemoveRotation.target")]
    public static RbNode<T>? Target<T>(RbLabels<T> n, bool right) => throw Ghost();
    [SpecOp("InductiveRemoveRotation.observed_target")]
    public static RbNode<T>? ObservedTarget<T>(RbLabels<T> n, bool right) => throw Ghost();
}

internal static class RbRemoveRotationProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveRotation.single $(nodes) $(right)")]
    [Requires("RbCursorSpec.Good(nodes) && RbRemoveRotationSpec.CanRotate(right ? RbRemovalRotation.Left : RbRemovalRotation.Right, nodes)")]
    [Ensures("RbCursorSpec.Member(nodes, RbRemoveRotationSpec.Target(nodes, right))")]
    [Ensures("RbRemoveRotationSpec.Target(nodes, right) == RbRemoveRotationSpec.ObservedTarget(nodes, right)")]
    [Ensures("RbCursorSpec.Top(RbRemoveRotationSpec.Prepared(nodes, right)) == RbCursorSpec.Top(nodes)")]
    [Ensures("RbCursorSpec.Same(right ? RbLocalSpec.RotateLeft(RbRemoveRotationSpec.Prepared(nodes, right)) : RbLocalSpec.RotateRight(RbRemoveRotationSpec.Prepared(nodes, right)), RbRemoveRotationSpec.Rotate(right ? RbRemovalRotation.Left : RbRemovalRotation.Right, nodes))")]
    public static void Single<T>(bool right, Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && root == RbCursorSpec.Top(nodes)")]
    [Requires("RbRemoveRotationSpec.CanRotate(rotation, nodes)")]
    [Ensures("RbCursorSpec.Owns(RbRemoveRotationSpec.Rotate(rotation, nodes))")]
    [Ensures("Result != null && Result == RbCursorSpec.Top(RbRemoveRotationSpec.Rotate(rotation, nodes))")]
    private static RbNode<T>? RotateRemovalLocal<T>(RbNode<T> root, RbRemovalRotation rotation,
        Ghost<RbLabels<T>> nodes = default)
    {
        RbCursorProof.Root(nodes);
        switch (rotation)
        {
            case RbRemovalRotation.Right:
            {
                RbNode<T>? child = LeftAt(root);
                RbNode<T>? removeRed = LeftAt(child!);
                RbRemoveRotationProof.Single(false, nodes);
                Pal.Assert(removeRed == RbRemoveRotationSpec.Target(nodes.Value, false));
                RecolorAt(removeRed, false);
                RbCursorProof.Change<T>(RbMutationSpec.Recolor(nodes.Value, removeRed, false),
                    RbRemoveRotationSpec.Prepared(nodes.Value, false));
                RbNode<T> result = RotateRightLocal(root);
                RbCursorProof.Change<T>(RbLocalSpec.RotateRight(RbRemoveRotationSpec.Prepared(nodes.Value, false)),
                    RbRemoveRotationSpec.Rotate(rotation, nodes.Value));
                return result;
            }
            case RbRemovalRotation.Left:
            {
                RbNode<T>? child = RightAt(root);
                RbNode<T>? removeRed = RightAt(child!);
                RbRemoveRotationProof.Single(true, nodes);
                Pal.Assert(removeRed == RbRemoveRotationSpec.Target(nodes.Value, true));
                RecolorAt(removeRed, false);
                RbCursorProof.Change<T>(RbMutationSpec.Recolor(nodes.Value, removeRed, false),
                    RbRemoveRotationSpec.Prepared(nodes.Value, true));
                RbNode<T> result = RotateLeftLocal(root);
                RbCursorProof.Change<T>(RbLocalSpec.RotateLeft(RbRemoveRotationSpec.Prepared(nodes.Value, true)),
                    RbRemoveRotationSpec.Rotate(rotation, nodes.Value));
                return result;
            }
            case RbRemovalRotation.RightLeft:
            {
                RbNode<T> result = RotateRightLeftLocal(root);
                RbCursorProof.Change<T>(RbLocalSpec.RotateRightLeft(nodes.Value),
                    RbRemoveRotationSpec.Rotate(rotation, nodes.Value));
                return result;
            }
            case RbRemovalRotation.LeftRight:
            {
                RbNode<T> result = RotateLeftRightLocal(root);
                RbCursorProof.Change<T>(RbLocalSpec.RotateLeftRight(nodes.Value),
                    RbRemoveRotationSpec.Rotate(rotation, nodes.Value));
                return result;
            }
            default:
                RbCursorProof.Change<T>(nodes, RbRemoveRotationSpec.Rotate(rotation, nodes.Value));
                return null;
        }
    }
}
