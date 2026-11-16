using System;
using System.Diagnostics;
using PalLang;

namespace PalCSharp.Tests.Inductive;

[SpecType("InductiveCursor.tree")]
public readonly struct RbLabels<T> { }

public static class RbCursorSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");

    [SpecOp("InductiveCursor.owns")]
    public static SlProp Owns<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("InductiveCursor.labelled")]
    public static SlProp Labelled<T>(RbNode<T>? root, SpecTree<(T, bool)> tree) => throw Ghost();
    [SpecOp("InductiveCursor.opened")]
    public static SlProp Opened<T>(RbLabels<T> nodes, RbNode<T>? current) => throw Ghost();
    [SpecOp("InductiveCursor.lookup")]
    public static SpecTree<(T, bool)> Lookup<T>(RbLabels<T> nodes, RbNode<T>? current) => throw Ghost();
    [SpecOp("InductiveCursor.member")]
    public static bool Member<T>(RbLabels<T> nodes, RbNode<T>? current) => throw Ghost();
    [SpecOp("InductiveCursor.good")]
    public static bool Good<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("InductiveCursor.same")]
    public static bool Same<T>(RbLabels<T> first, RbLabels<T> second) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.RegionPath.top")]
    public static RbNode<T>? Top<T>(RbLabels<T> nodes) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.strip")]
    public static SpecTree<(T, bool)> Strip<T>(RbLabels<T> nodes) => throw Ghost();
}

public static class RbCursorProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveCursor.change $(before) $(after)")]
    [Requires("RbCursorSpec.Owns(before)")]
    [Requires("RbCursorSpec.Same(before, after)")]
    [Ensures("RbCursorSpec.Owns(after)")]
    public static void Change<T>(Ghost<RbLabels<T>> before, Ghost<RbLabels<T>> after) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveCursor.facts $(nodes)")]
    [Preserves("RbCursorSpec.Owns(nodes)")]
    [Ensures("RbCursorSpec.Good(nodes)")]
    public static void Facts<T>(Ghost<RbLabels<T>> nodes) { }
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveCursor.label_public $(root) $(tree)")]
    [Requires("RbSpec.Holds(root, tree)")]
    [Ensures("RbCursorSpec.Labelled(root, tree)")]
    public static void Label<T>(RbNode<T>? root, Ghost<SpecTree<(T, bool)>> tree) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveCursor.unlabel_exists $(root) $(tree)")]
    [Requires("RbCursorSpec.Labelled(root, tree)")]
    [Ensures("RbSpec.Holds(root, tree)")]
    public static void Unlabel<T>(RbNode<T>? root, Ghost<SpecTree<(T, bool)>> tree) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveCursor.lookup_root $(nodes)")]
    [Requires("RbCursorSpec.Good(nodes)")]
    [Ensures("RbCursorSpec.Lookup(nodes, RbCursorSpec.Top(nodes)) == RbCursorSpec.Strip(nodes)")]
    [Ensures("Pal.Implies(RbCursorSpec.Top(nodes) != null, RbCursorSpec.Member(nodes, RbCursorSpec.Top(nodes)))")]
    [Ensures("RbCursorSpec.Lookup(nodes, null).IsLeaf")]
    public static void Root<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveCursor.open_node $(nodes) $(current)")]
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, current)")]
    [Ensures("RbCursorSpec.Opened(nodes, current)")]
    public static void Open<T>(RbNode<T> current, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveCursor.close_node $(nodes) $(current)")]
    [Requires("RbCursorSpec.Opened(nodes, current)")]
    [Ensures("RbCursorSpec.Owns(nodes)")]
    public static void Close<T>(RbNode<T> current, Ghost<RbLabels<T>> nodes) { }
}
