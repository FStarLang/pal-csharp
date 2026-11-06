using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R27.26. Top-down red-black insertion over the heap of a region whose class
/// <c>K</c> (each method's first type argument) is a node of a red-black
/// tree viewed as <c>(T, bool)</c>, its key and whether it is red: the loop invariant of
/// <c>SortedSet&lt;T&gt;.AddIfNotPresent</c>, what <c>Node</c>'s helpers do to the tree of
/// boxes a pointer reaches, and the ghost steps between them.
/// <c>Pulse.Lib.CSharp.TopDownHeap</c>; every member is a <see cref="RegionOpAttribute"/>
/// (a <c>void</c> one is a lemma, called as a ghost statement) except <see cref="Inserted"/>.
/// <c>order</c> arguments are the program's <c>comparer.Compare</c> results: only their
/// sign is used.
/// </summary>
public static class SpecTopDown
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecTopDown is a specification-only construct and has no runtime meaning.");

    // What `Node`'s helpers do.

    /// <summary><c>ColorBlack</c>/<c>ColorRed</c>: <paramref name="x"/>'s colour set, every box where it was.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.recolored")]
    public static bool Recolored<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? x, bool red) where K : class => throw Ghost();

    /// <summary><c>Split4Node</c>, every box where it was.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.split4ed")]
    public static bool Split4ed<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? x) where K : class => throw Ghost();

    /// <summary>
    /// The rotation from <paramref name="x"/> to the new top <paramref name="y"/> that the
    /// sides <paramref name="w0"/> (<c>currentIsOnRight</c>) and <paramref name="w1"/>
    /// (<c>parentIsOnRight</c>) choose: both true <c>RotateLeft</c>, both false
    /// <c>RotateRight</c>, true/false <c>RotateLeftRight</c>, false/true <c>RotateRightLeft</c>.
    /// </summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.rotated")]
    public static bool Rotated<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? x, K? y, bool w0, bool w1) where K : class => throw Ghost();

    /// <summary><c>ReplaceChild(c, c2)</c> on <paramref name="p"/>: its link to <paramref name="c"/> now <paramref name="c2"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionPath.relinked")]
    public static bool Relinked<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? p, K? c, K? c2) where K : class => throw Ghost();

    /// <summary><c>ReplaceChildOrRoot(p, c, c2)</c>: the root becomes <paramref name="c2"/> when <paramref name="p"/> is null.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.replaced")]
    public static bool Replaced<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? root0, K? root1, K? p, K? c, K? c2) where K : class => throw Ghost();

    // The descent.

    /// <summary>The loop invariant: a set of <paramref name="k0"/> red-black but for its root, and a valid 2-3-4 descent to <paramref name="cur"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.inv")]
    public static bool Inv<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? ggp, SpecInt order) where K : class => throw Ghost();

    /// <summary>The loop's measure.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.measure")]
    public static SpecInt Measure<K, T>(IComparer<T> c, T k, SpecHeap<K> h, K? root, K? cur) where K : class => throw Ghost();

    /// <summary>The end of an iteration: the invariant one node down, below the measure <paramref name="m0"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.ready")]
    public static bool Ready<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, SpecInt order, SpecInt m0) where K : class => throw Ghost();

    /// <summary>After a split under a red parent: <c>InsertionBalance</c> is due.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.pending")]
    public static bool Pending<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? ggp, SpecInt order, SpecInt m0) where K : class => throw Ghost();

    /// <summary><c>IsNonNullRed(par)</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.par_red")]
    public static bool ParRed<K, T>(SpecHeap<K> h, K? par) where K : class => throw Ghost();

    /// <summary><c>InsertionBalance</c>'s precondition.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.balance_pre")]
    public static bool BalancePre<K, T>(SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? ggp) where K : class => throw Ghost();

    /// <summary><c>InsertionBalance</c>'s postcondition.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.balanced")]
    public static bool Balanced<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? root0, K? root1, K? cur, K? par0, K? par1, K? ggp) where K : class => throw Ghost();

    /// <summary>The sides the search took at the parent and the grandparent.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.bal_sides")]
    public static bool BalSides<K, T>(SpecHeap<K> h, K? root, K? cur, bool w0, bool w1) where K : class => throw Ghost();

    /// <summary>The tree at <paramref name="root"/> is a set of <paramref name="k1"/>, red-black but for its root.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.okp")]
    public static bool Okp<K, T>(IComparer<T> c, Seq<T> k1, SpecHeap<K> h, K? root) where K : class => throw Ghost();

    /// <summary><paramref name="k0"/> with <paramref name="k"/> inserted at its lower bound.</summary>
    [SpecOp("Pulse.Lib.CSharp.TopDownHeap.inserted")]
    public static Seq<T> Inserted<T>(IComparer<T> c, Seq<T> k0, T k) => throw Ghost();

    // The ghost steps.

    /// <summary>Before the loop: the invariant at a non-null root.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.start")]
    public static void Start<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root) where K : class => throw Ghost();

    /// <summary>The top of an iteration: <paramref name="cur"/> can be read.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.at_cur")]
    public static void AtCur<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? ggp, SpecInt order) where K : class => throw Ghost();

    /// <summary>After the comparison: found, or (without a split) the iteration is done.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.look")]
    public static void Look<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? ggp, SpecInt order0, SpecInt order) where K : class => throw Ghost();

    /// <summary>After <c>Split4Node</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.split")]
    public static void Split<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, K? root, K? cur, K? par, K? gp, K? ggp, SpecInt order0, SpecInt order) where K : class => throw Ghost();

    /// <summary>After the loop's <c>InsertionBalance</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.after_balance")]
    public static void AfterBalance<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h2, K? root, K? root2, K? cur, K? par, K? par2, K? gp, K? ggp, SpecInt order, SpecInt m0) where K : class => throw Ghost();

    /// <summary><c>InsertionBalance</c>'s start: the parent and grandparent can be read.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.bal_start")]
    public static void BalStart<K, T>(SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? ggp) where K : class => throw Ghost();

    /// <summary><c>InsertionBalance</c>'s great-grandparent, when not null, can be re-linked.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.bal_ggp")]
    public static void BalGgp<K, T>(SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? ggp) where K : class => throw Ghost();

    /// <summary>What <c>parentIsOnRight</c> and <c>currentIsOnRight</c> tell.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.bal_rot")]
    public static void BalRot<K, T>(SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? ggp, bool w0, bool w1) where K : class => throw Ghost();

    /// <summary>After the rotation.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.bal_mid")]
    public static void BalMid<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? root, K? cur, K? par, K? gp, K? ggp, K? y, bool w0, bool w1) where K : class => throw Ghost();

    /// <summary>After <c>grandParent.ColorRed()</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.bal_red")]
    public static void BalRed<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, SpecHeap<K> h2, K? root, K? cur, K? par, K? gp, K? ggp, K? y, bool w0, bool w1) where K : class => throw Ghost();

    /// <summary>The end of <c>InsertionBalance</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.bal_end")]
    public static void BalEnd<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, SpecHeap<K> h2, SpecHeap<K> h3, SpecHeap<K> h4, K? root0, K? root1, K? cur, K? par0, K? par1, K? gp, K? ggp, K? y, bool w0, bool w1) where K : class => throw Ghost();

    /// <summary>The loop is done: the parent the new node hangs from.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.at_end")]
    public static void AtEnd<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? par, K? gp, K? ggp, SpecInt order) where K : class => throw Ghost();

    /// <summary>The new red node linked under the parent.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.linked_leaf")]
    public static void LinkedLeaf<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h2, K? root, K? x, K? par, K? gp, K? ggp, SpecInt order) where K : class => throw Ghost();

    /// <summary>After the final <c>InsertionBalance</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.after_insert_balance")]
    public static void AfterInsertBalance<K, T>(IComparer<T> c, Seq<T> k1, SpecHeap<K> h2, SpecHeap<K> h3, K? root, K? root3, K? x, K? par, K? par3, K? ggp) where K : class => throw Ghost();

    /// <summary><c>root.ColorBlack()</c> after an insertion.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.finish_ok")]
    public static void FinishOk<K, T>(IComparer<T> c, Seq<T> k1, SpecHeap<K> h0, SpecHeap<K> h1, K? root) where K : class => throw Ghost();

    /// <summary><c>root.ColorBlack()</c> when the key was found.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownHeap.finish")]
    public static void Finish<K, T>(IComparer<T> c, Seq<T> k0, SpecHeap<K> h0, SpecHeap<K> h1, K? root) where K : class => throw Ghost();
}
