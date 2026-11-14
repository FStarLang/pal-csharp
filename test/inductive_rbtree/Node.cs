using System;
using System.Collections.Generic;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveModel.fst")]
[assembly: IncludePulseFile("InductiveOrder.fst")]
[assembly: IncludePulseFile("InductiveOwnership.fst")]
[assembly: IncludePulseFile("InductiveCursor.fst")]

namespace PalCSharp.Tests.Inductive;

// Plain cells, owned only by recursive separating predicates and ghost contexts.
[Plain]
public sealed class RbNode<T>
{
    internal T key = default!;
    internal bool red;
    internal RbNode<T>? left;
    internal RbNode<T>? right;
}

public static class RbSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("InductiveOwnership.holds")]
    public static SlProp Holds<T>(RbNode<T>? node, SpecTree<(T, bool)> tree) => throw Ghost();
    [SpecOp("InductiveOwnership.opened")]
    public static SlProp Opened<T>(RbNode<T>? node, SpecTree<(T, bool)> tree) => throw Ghost();
    [SpecOp("InductiveOwnership.held")]
    public static SlProp Held<T>(RbNode<T>? node, T key, bool red, RbNode<T>? left, RbNode<T>? right) => throw Ghost();
    [SpecOp("InductiveModel.left")]
    public static SpecTree<(T, bool)> Left<T>(SpecTree<(T, bool)> t) => throw Ghost();
    [SpecOp("InductiveModel.right")]
    public static SpecTree<(T, bool)> Right<T>(SpecTree<(T, bool)> t) => throw Ghost();
    [SpecOp("InductiveModel.node")]
    public static SpecTree<(T, bool)> Node<T>(SpecTree<(T, bool)> l, T k, bool red, SpecTree<(T, bool)> r) => throw Ghost();
    [SpecOp("InductiveOrder.adds_exactly")]
    public static bool AddsExactly<T>(IComparer<T> c, SpecTree<(T, bool)> t, T k, SpecTree<(T, bool)> result) => throw Ghost();
    [SpecOp("InductiveOwnership.detached")]
    public static SlProp Detached<T>(RbNode<T>? node) => throw Ghost();
}

public static class RbProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("Pulse.Lib.CSharp.SearchTree.contains_keys $(comparer) $(tree) $(key)")]
    [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(tree))")]
    [Ensures("SpecSearchTree.Contains(comparer, tree, key) == (Pal.KeyIndex(comparer, SpecSearchTree.Keys(tree), key) >= 0)")]
    public static void ContainsKeys<T>(IComparer<T> comparer, Ghost<SpecTree<(T, bool)>> tree, T key) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveOwnership.empty #$(T) ()")]
    [Ensures("RbSpec.Holds<T>(null, SpecTree.Leaf<(T, bool)>())")]
    public static void Empty<T>() { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveOwnership.cases $(root) $(tree)")]
    [Preserves("RbSpec.Holds(root, tree)")]
    [Ensures("Pal.Iff(root == null, tree.IsLeaf)")]
    public static void Cases<T>(RbNode<T>? root, Ghost<SpecTree<(T, bool)>> tree) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveOwnership.open_tree $(root) $(tree)")]
    [Requires("RbSpec.Holds(root, tree)")]
    [Requires("!tree.IsLeaf")]
    [Ensures("RbSpec.Opened(root, tree)")]
    [Ensures("root != null")]
    public static void Open<T>(RbNode<T>? root, Ghost<SpecTree<(T, bool)>> tree) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveOwnership.close_tree $(root) $(key) $(red) $(left) $(right) $(lt) $(rt)")]
    [Requires("RbSpec.Held(root, key, red, left, right)")]
    [Requires("RbSpec.Holds(left, lt)")]
    [Requires("RbSpec.Holds(right, rt)")]
    [Ensures("RbSpec.Holds(root, RbSpec.Node(lt, key, red, rt))")]
    public static void Close<T>(RbNode<T>? root, T key, bool red, RbNode<T>? left, RbNode<T>? right,
        Ghost<SpecTree<(T, bool)>> lt, Ghost<SpecTree<(T, bool)>> rt) { }
}
