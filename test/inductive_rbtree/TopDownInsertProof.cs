using System;
using System.Collections.Generic;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveInsert.fst")]
[assembly: IncludePulseFile("InductiveInsertResult.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbAddSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("InductiveInsert.empty_keys")]
    public static Seq<T> EmptyKeys<T>() => throw Ghost();
    [SpecOp("InductiveInsertResult.added")]
    public static SlProp Added<T>(RbNode<T>? root, IComparer<T> c, SpecTree<(T, bool)> before, T key) => throw Ghost();
    [SpecOp("InductiveInsertResult.labelled")]
    public static SlProp Labelled<T>(RbNode<T>? root, IComparer<T> c, Seq<T> keys, T key) => throw Ghost();
    [SpecOp("InductiveInsert.complete")]
    public static bool Complete<T>(IComparer<T> c, Seq<T> keys, T key, RbNode<T>? root, RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveInsert.expected")]
    public static Seq<T> Expected<T>(IComparer<T> c, Seq<T> keys, T key) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDown.ok")]
    public static bool Ok<T>(IComparer<T> c, Seq<T> keys, RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveInsert.inv")]
    public static bool Inv<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order) => throw Ghost();
    [SpecOp("InductiveInsert.ready")]
    public static bool Ready<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, SpecInt order, SpecInt measure) => throw Ghost();
    [SpecOp("InductiveInsert.pending")]
    public static bool Pending<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order, SpecInt measure) => throw Ghost();
    [SpecOp("InductiveInsert.measure")]
    public static SpecInt Measure<T>(IComparer<T> c, T key, RbLabels<T> n, RbNode<T>? cur) => throw Ghost();
    [SpecOp("InductiveInsert.comparison")]
    public static SpecInt Comparison<T>(IComparer<T> c, T key, RbLabels<T> n, RbNode<T>? cur) => throw Ghost();
    [SpecOp("InductiveInsert.split_tree")]
    public static RbLabels<T> Split<T>(RbLabels<T> n, RbNode<T> cur) => throw Ghost();
    [SpecOp("InductiveInsert.split_result")]
    public static bool SplitResult<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order) => throw Ghost();
    [SpecOp("InductiveInsert.linked_result")]
    public static bool LinkedResult<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T> node, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order) => throw Ghost();
}

public static class RbAddProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.advance $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(next) $(order) $(measure)")]
    [Requires("RbAddSpec.Ready(comparer, keys, key, nodes, cur, par, gp, order, measure)")]
    [Requires("next == (order < 0 ? RbCursorSpec.Top(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, cur))) : RbCursorSpec.Top(RbLocalSpec.Right(RbLinkSpec.Sub(nodes, cur))))")]
    [Ensures("RbAddSpec.Inv(comparer, keys, key, nodes, next, cur, par, gp, order)")]
    [Ensures("0 <= RbAddSpec.Measure(comparer, key, nodes, next) && RbAddSpec.Measure(comparer, key, nodes, next) < measure")]
    public static void Advance<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T> cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? next, SpecInt order, SpecInt measure) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.balance_nodes $(nodes) $(cur) $(par) $(gp) $(ggp)")]
    [Requires("RbBalanceSpec.Ready(nodes, cur, par, gp, ggp)")]
    [Ensures("par != null && gp != null")]
    public static void BalanceNodes<T>(RbNode<T> cur, RbNode<T>? par, RbNode<T>? gp,
        RbNode<T>? ggp, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsertResult.publish $(root) $(comparer) $(tree) $(key)")]
    [Requires("RbAddSpec.Labelled(root, comparer, SpecSearchTree.Keys(tree), key)")]
    [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(tree))")]
    [Ensures("RbAddSpec.Added(root, comparer, tree, key)")]
    public static void Publish<T>(RbNode<T>? root, IComparer<T> comparer, T key, Ghost<SpecTree<(T, bool)>> tree) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsertResult.release_empty $(nodes)")]
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbCursorSpec.Top(nodes) == null")]
    [Ensures("!RbLocalSpec.Branch(nodes)")]
    public static void ReleaseEmpty<T>(Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsertResult.singleton $(comparer) $(key) $(node)")]
    [Requires("node != null")]
    [Ensures("RbAddSpec.Complete(comparer, RbAddSpec.EmptyKeys<T>(), key, node, RbSplitSpec.Color(RbLeafSpec.Leaf(node, key), false))")]
    public static void Singleton<T>(RbNode<T> node, IComparer<T> comparer, T key) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.start $(comparer) $(key) $(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && RbLocalSpec.Branch(nodes)")]
    [Requires("SpecSearchTree.IsRedBlack(RbCursorSpec.Strip(nodes)) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)))")]
    [Ensures("RbAddSpec.Inv(comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)), key, nodes, RbCursorSpec.Top(nodes), null, null, null, 0)")]
    public static void Start<T>(IComparer<T> comparer, T key, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.at_cur $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(ggp) $(order)")]
    [Requires("RbAddSpec.Inv(comparer, keys, key, nodes, cur, par, gp, ggp, order) && cur != null")]
    [Ensures("RbCursorSpec.Member(nodes, cur)")]
    public static void AtCur<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.look $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(ggp) $(order0) $(order)")]
    [Requires("RbAddSpec.Inv(comparer, keys, key, nodes, cur, par, gp, ggp, order0) && cur != null")]
    [Requires("order == RbAddSpec.Comparison(comparer, key, nodes, cur)")]
    [Ensures("Pal.Implies(order == 0, Pal.KeyIndex(comparer, keys, key) >= 0)")]
    [Ensures("Pal.Implies(order != 0 && !RbSplitSpec.Is4(RbLinkSpec.Sub(nodes, cur)), RbAddSpec.Ready(comparer, keys, key, nodes, cur, par, gp, order, RbAddSpec.Measure(comparer, key, nodes, cur)))")]
    public static void Look<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order0, SpecInt order) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.split_step $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(ggp) $(order0) $(order)")]
    [Requires("RbAddSpec.Inv(comparer, keys, key, nodes, cur, par, gp, ggp, order0) && cur != null")]
    [Requires("order == RbAddSpec.Comparison(comparer, key, nodes, cur) && order != 0 && RbSplitSpec.Is4(RbLinkSpec.Sub(nodes, cur))")]
    [Ensures("RbAddSpec.SplitResult(comparer, keys, key, nodes, cur, par, gp, ggp, order)")]
    public static void Split<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order0, SpecInt order) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.at_end $(comparer) $(keys) $(key) $(nodes) $(par) $(gp) $(ggp) $(order)")]
    [Requires("RbAddSpec.Inv(comparer, keys, key, nodes, null, par, gp, ggp, order)")]
    [Ensures("par != null && RbCursorSpec.Member(nodes, par)")]
    [Ensures("!(order > 0 ? RbLocalSpec.Branch(RbLocalSpec.Right(RbLinkSpec.Sub(nodes, par))) : RbLocalSpec.Branch(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, par))))")]
    public static void AtEnd<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.linked_leaf $(comparer) $(keys) $(key) $(nodes) $(node) $(par) $(gp) $(ggp) $(order)")]
    [Requires("RbAddSpec.Inv(comparer, keys, key, nodes, null, par, gp, ggp, order)")]
    [Requires("node != null && !RbCursorSpec.Member(nodes, node)")]
    [Ensures("RbAddSpec.LinkedResult(comparer, keys, key, nodes, node, par, gp, ggp, order)")]
    public static void Linked<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T> node, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? ggp, SpecInt order) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveInsert.finish $(comparer) $(keys) $(key) $(nodes)")]
    [Requires("RbAddSpec.Ok(comparer, RbAddSpec.Expected(comparer, keys, key), nodes)")]
    [Ensures("RbAddSpec.Complete(comparer, keys, key, RbCursorSpec.Top(nodes), RbSplitSpec.Color(nodes, false))")]
    public static void Finish<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes) { }
}
