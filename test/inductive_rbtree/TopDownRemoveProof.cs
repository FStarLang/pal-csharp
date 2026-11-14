using System;
using System.Collections.Generic;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("InductiveRemove.fst")]
[assembly: IncludePulseFile("InductiveRemoveRepair.fst")]
[assembly: IncludePulseFile("InductiveRemoveResult.fst")]

namespace PalCSharp.Tests.Inductive;

public static class RbRemoveSpec
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("InductiveRemoveResult.removed")]
    public static SlProp Removed<T>(RbNode<T>? root, IComparer<T> c, SpecTree<(T, bool)> before, T key) => throw Ghost();
    [SpecOp("InductiveRemoveResult.labelled")]
    public static SlProp Labelled<T>(RbNode<T>? root, IComparer<T> c, Seq<T> keys, T key) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDownRemove.removed")]
    public static Seq<T> Expected<T>(IComparer<T> c, Seq<T> keys, T key) => throw Ghost();
    [SpecOp("InductiveRemove.inv")]
    public static bool Inv<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found) => throw Ghost();
    [SpecOp("InductiveRemove.mid")]
    public static bool Mid<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found, SpecInt measure) => throw Ghost();
    [SpecOp("InductiveRemove.fixed")]
    public static bool Fixed<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? match, RbNode<T>? pom, bool found, SpecInt measure) => throw Ghost();
    [SpecOp("InductiveRemoveResult.after")]
    public static bool After<T>(IComparer<T> c, Seq<T> keys, T key, RbLabels<T> n,
        RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom) => throw Ghost();
    [SpecOp("InductiveRemoveResult.complete")]
    public static bool Complete<T>(IComparer<T> c, Seq<T> keys, T key, RbNode<T>? root, RbLabels<T> n) => throw Ghost();
    [SpecOp("InductiveRemove.measure")]
    public static SpecInt Measure<T>(RbLabels<T> n, RbNode<T>? cur) => throw Ghost();
    [SpecOp("InductiveRemove.order")]
    public static SpecInt Order<T>(IComparer<T> c, T key, RbLabels<T> n, RbNode<T>? cur, bool found) => throw Ghost();
    [SpecOp("InductiveRemove.next")]
    public static RbNode<T>? Next<T>(RbLabels<T> n, RbNode<T>? cur, SpecInt order) => throw Ghost();
    [SpecOp("InductiveRemove.sibling")]
    public static RbNode<T>? Sibling<T>(RbLabels<T> n, RbNode<T>? par, RbNode<T>? cur) => throw Ghost();
    [SpecOp("InductiveRemove.merged")]
    public static RbLabels<T> Merged<T>(RbLabels<T> n, RbNode<T>? par) => throw Ghost();
    [SpecOp("InductiveRemoveRepair.lifted")]
    public static RbLabels<T> Lifted<T>(RbLabels<T> n, RbNode<T>? par, RbNode<T>? cur) => throw Ghost();
    [SpecOp("InductiveRemoveRepair.borrowed")]
    public static RbLabels<T> Borrowed<T>(RbLabels<T> n, RbNode<T>? par, RbNode<T>? cur) => throw Ghost();
    [SpecOp("InductiveRemoveRepair.rotation")]
    internal static RbRemovalRotation Rotation<T>(RbLabels<T> n, RbNode<T>? par, RbNode<T>? cur) => throw Ghost();
    [SpecOp("InductiveRemoveRepair.new_parent")]
    public static RbNode<T>? NewParent<T>(RbLabels<T> n, RbNode<T>? par, RbNode<T>? cur) => throw Ghost();
    [SpecOp("Pulse.Lib.CSharp.TopDownRemove.pom_a")]
    public static RbNode<T>? NewMatchParent<T>(RbNode<T>? par, RbNode<T>? match, RbNode<T>? newParent, RbNode<T>? pom) => throw Ghost();
}

public static class RbRemoveProof
{
    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveResult.null_detached $(node)")]
    [Requires("node == null")]
    [Ensures("RbSpec.Detached(node)")]
    public static void NullDetached<T>(RbNode<T>? node) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemove.start $(comparer) $(key) $(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && SpecSearchTree.IsRedBlack(RbCursorSpec.Strip(nodes)) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)))")]
    [Ensures("RbRemoveSpec.Inv(comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)), key, nodes, RbCursorSpec.Top(nodes), null, null, null, null, false)")]
    public static void Start<T>(IComparer<T> comparer, T key, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemove.at_cur $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found)")]
    [Requires("RbRemoveSpec.Inv(comparer, keys, key, nodes, cur, par, gp, match, pom, found) && cur != null")]
    [Ensures("RbCursorSpec.Good(nodes) && RbCursorSpec.Member(nodes, cur) && RbLinkSpec.Parent(nodes, cur) == par")]
    [Ensures("Pal.Implies(par == null, cur == RbCursorSpec.Top(nodes))")]
    [Ensures("Pal.Implies(par != null, RbCursorSpec.Member(nodes, par) && RbLinkSpec.Parent(nodes, par) == gp)")]
    public static void AtCur<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemove.not2 $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found)")]
    [Requires("RbRemoveSpec.Inv(comparer, keys, key, nodes, cur, par, gp, match, pom, found) && cur != null && !RbRemoveLocalSpec.Is2(RbLinkSpec.Sub(nodes, cur))")]
    [Ensures("RbRemoveSpec.Fixed(comparer, keys, key, nodes, cur, par, match, pom, found, RbRemoveSpec.Measure(nodes, cur))")]
    public static void Not2<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemove.root $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found)")]
    [Requires("RbRemoveSpec.Inv(comparer, keys, key, nodes, cur, par, gp, match, pom, found) && cur != null && par == null && RbRemoveLocalSpec.Is2(RbLinkSpec.Sub(nodes, cur))")]
    [Ensures("RbRemoveSpec.Fixed(comparer, keys, key, RbMutationSpec.Recolor(nodes, cur, true), cur, par, match, pom, found, RbRemoveSpec.Measure(nodes, cur))")]
    public static void Root<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveRepair.at_sib $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found)")]
    [Requires("RbRemoveSpec.Inv(comparer, keys, key, nodes, cur, par, gp, match, pom, found) && cur != null && par != null && RbRemoveLocalSpec.Is2(RbLinkSpec.Sub(nodes, cur))")]
    [Ensures("RbRemoveSpec.Sibling(nodes, par, cur) != null && RbCursorSpec.Member(nodes, RbRemoveSpec.Sibling(nodes, par, cur))")]
    [Ensures("RbLiftSpec.Child(RbLinkSpec.Sub(nodes, par), RbRemoveSpec.Sibling(nodes, par, cur)!)")]
    public static void AtSibling<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemove.direct $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found)")]
    [Requires("RbRemoveSpec.Inv(comparer, keys, key, nodes, cur, par, gp, match, pom, found) && cur != null && par != null && RbRemoveLocalSpec.Is2(RbLinkSpec.Sub(nodes, cur))")]
    [Requires("!SpecSearchTree.IsRed(RbCursorSpec.Lookup(nodes, RbRemoveSpec.Sibling(nodes, par, cur)))")]
    [Ensures("RbRemoveSpec.Mid(comparer, keys, key, nodes, cur, par, gp, match, pom, found, RbRemoveSpec.Measure(nodes, cur))")]
    public static void Direct<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveRepair.lift $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found)")]
    [Requires("RbRemoveSpec.Inv(comparer, keys, key, nodes, cur, par, gp, match, pom, found) && cur != null && par != null && RbRemoveLocalSpec.Is2(RbLinkSpec.Sub(nodes, cur))")]
    [Requires("SpecSearchTree.IsRed(RbCursorSpec.Lookup(nodes, RbRemoveSpec.Sibling(nodes, par, cur)))")]
    [Ensures("RbRemoveSpec.Mid(comparer, keys, key, RbRemoveSpec.Lifted(nodes, par, cur), cur, par, RbRemoveSpec.Sibling(nodes, par, cur), match, RbRemoveSpec.NewMatchParent(par, match, RbRemoveSpec.Sibling(nodes, par, cur), pom), found, RbRemoveSpec.Measure(nodes, cur))")]
    public static void Lift<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveRepair.at_mid $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found) $(measure)")]
    [Requires("RbRemoveSpec.Mid(comparer, keys, key, nodes, cur, par, gp, match, pom, found, measure)")]
    [Ensures("RbCursorSpec.Good(nodes) && cur != null && par != null && RbRemoveSpec.Sibling(nodes, par, cur) != null")]
    [Ensures("RbCursorSpec.Member(nodes, cur) && RbCursorSpec.Member(nodes, par) && RbCursorSpec.Member(nodes, RbRemoveSpec.Sibling(nodes, par, cur)) && RbLinkSpec.Parent(nodes, par) == gp")]
    [Ensures("RbLocalSpec.Branch(RbLocalSpec.Left(RbLinkSpec.Sub(nodes, par))) && RbLocalSpec.Branch(RbLocalSpec.Right(RbLinkSpec.Sub(nodes, par)))")]
    public static void AtMid<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found, SpecInt measure) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemove.merge $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found) $(measure)")]
    [Requires("RbRemoveSpec.Mid(comparer, keys, key, nodes, cur, par, gp, match, pom, found, measure) && RbRemoveLocalSpec.Is2(RbLinkSpec.Sub(nodes, RbRemoveSpec.Sibling(nodes, par, cur)))")]
    [Ensures("RbRemoveSpec.Fixed(comparer, keys, key, RbRemoveSpec.Merged(nodes, par), cur, par, match, pom, found, measure)")]
    [Ensures("RbCursorSpec.Top(RbRemoveSpec.Merged(nodes, par)) == RbCursorSpec.Top(nodes)")]
    public static void Merge<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found, SpecInt measure) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveRepair.borrow $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(gp) $(match) $(pom) $(found) $(measure)")]
    [Requires("RbRemoveSpec.Mid(comparer, keys, key, nodes, cur, par, gp, match, pom, found, measure) && !RbRemoveLocalSpec.Is2(RbLinkSpec.Sub(nodes, RbRemoveSpec.Sibling(nodes, par, cur)))")]
    [Ensures("RbBorrowSpec.Ready(RbLinkSpec.Sub(nodes, par), cur!, RbRemoveSpec.Rotation(nodes, par, cur))")]
    [Ensures("RbRemoveSpec.Fixed(comparer, keys, key, RbRemoveSpec.Borrowed(nodes, par, cur), cur, par, match, RbRemoveSpec.NewMatchParent(par, match, RbRemoveSpec.NewParent(nodes, par, cur), pom), found, measure)")]
    public static void Borrow<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found, SpecInt measure) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemove.at_fixed $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(match) $(pom) $(found) $(measure)")]
    [Requires("RbRemoveSpec.Fixed(comparer, keys, key, nodes, cur, par, match, pom, found, measure)")]
    [Ensures("RbCursorSpec.Good(nodes) && cur != null && RbCursorSpec.Member(nodes, cur)")]
    public static void AtFixed<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? match, RbNode<T>? pom, bool found, SpecInt measure) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemove.advance $(comparer) $(keys) $(key) $(nodes) $(cur) $(par) $(match) $(pom) $(found) $(measure) $(order)")]
    [Requires("RbRemoveSpec.Fixed(comparer, keys, key, nodes, cur, par, match, pom, found, measure) && order == RbRemoveSpec.Order(comparer, key, nodes, cur, found)")]
    [Ensures("RbRemoveSpec.Inv(comparer, keys, key, nodes, RbRemoveSpec.Next(nodes, cur, order), cur, par, order == 0 ? cur : match, order == 0 ? par : pom, found || order == 0)")]
    [Ensures("0 <= RbRemoveSpec.Measure(nodes, RbRemoveSpec.Next(nodes, cur, order)) && RbRemoveSpec.Measure(nodes, RbRemoveSpec.Next(nodes, cur, order)) < measure")]
    public static void Advance<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? cur, RbNode<T>? par, RbNode<T>? match, RbNode<T>? pom, bool found, SpecInt measure, SpecInt order) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveResult.end_search $(comparer) $(keys) $(key) $(nodes) $(par) $(gp) $(match) $(pom) $(found)")]
    [Requires("RbRemoveSpec.Inv(comparer, keys, key, nodes, null, par, gp, match, pom, found)")]
    [Ensures("RbRemoveSpec.After(comparer, keys, key, nodes, par, gp, match, pom)")]
    public static void End<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes,
        RbNode<T>? par, RbNode<T>? gp, RbNode<T>? match, RbNode<T>? pom, bool found) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveResult.finish $(comparer) $(keys) $(key) $(nodes)")]
    [Requires("RbAddSpec.Ok(comparer, RbRemoveSpec.Expected(comparer, keys, key), nodes)")]
    [Ensures("RbRemoveSpec.Complete(comparer, keys, key, RbCursorSpec.Top(nodes), RbSplitSpec.Color(nodes, false))")]
    [Ensures("RbCursorSpec.Same(RbMutationSpec.Recolor(nodes, RbCursorSpec.Top(nodes), false), RbSplitSpec.Color(nodes, false))")]
    public static void Finish<T>(IComparer<T> comparer, Ghost<Seq<T>> keys, T key, Ghost<RbLabels<T>> nodes) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("InductiveRemoveResult.publish $(root) $(comparer) $(tree) $(key)")]
    [Requires("RbRemoveSpec.Labelled(root, comparer, SpecSearchTree.Keys(tree), key)")]
    [Requires("Pal.StrictlySorted(comparer, SpecSearchTree.Keys(tree))")]
    [Ensures("RbRemoveSpec.Removed(root, comparer, tree, key)")]
    public static void Publish<T>(RbNode<T>? root, IComparer<T> comparer, T key, Ghost<SpecTree<(T, bool)>> tree) { }
}
