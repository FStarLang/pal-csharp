using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveMutation.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbMutationSpec
{
    [SpecOp("InductiveMutation.recolor")]
    public static RbLabels<T> Recolor<T>(RbLabels<T> nodes, RbNode<T>? current, bool red) =>
        throw new InvalidOperationException("Specification only");

    [SpecOp("InductiveMutation.color_opened")]
    public static SlProp ColorOpened<T>(RbLabels<T> nodes, RbNode<T>? current, bool red) =>
        throw new InvalidOperationException("Specification only");
}

public static class RbMutationProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveMutation.null_color $(nodes) $(current) $(red)")]
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("current == null")]
    [Ensures("RbCursorSpec.Owns(RbMutationSpec.Recolor(nodes, current, red))")]
    public static void NullColor<T>(RbNode<T>? current, bool red, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveMutation.close_color $(nodes) $(current) $(red)")]
    [Requires("RbMutationSpec.ColorOpened(nodes, current, red)")]
    [Ensures("RbCursorSpec.Owns(RbMutationSpec.Recolor(nodes, current, red))")]
    public static void CloseColor<T>(RbNode<T> current, bool red, Ghost<RbLabels<T>> nodes) { }
}

public static partial class RbTree
{
    // One concrete write, including when the existing colour already equals red.
    // The focus and universally quantified restoration trade are entirely ghost.
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes)")]
    [Requires("current == null || RbCursorSpec.Member(nodes, current)")]
    [Ensures("RbCursorSpec.Owns(RbMutationSpec.Recolor(nodes, current, red))")]
    public static void RecolorAt<T>(RbNode<T>? current, bool red,
        Ghost<RbLabels<T>> nodes = default)
    {
        if (current != null)
        {
            RbCursorProof.Open(current, nodes);
            current.red = red;
            RbMutationProof.CloseColor(current, red, nodes);
        }
        else
        {
            RbMutationProof.NullColor(current, red, nodes);
        }
    }
}
