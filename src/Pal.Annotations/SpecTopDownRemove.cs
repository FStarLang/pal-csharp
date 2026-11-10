using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R27.30. Top-down red-black removal over the heap of a region whose class
/// <c>K</c> (each method's first type argument) is a node of a red-black tree
/// viewed as <c>(T, bool)</c>: the loop invariant of <c>SortedSet&lt;T&gt;.DoRemove</c>, what
/// <c>ReplaceNode</c> does, and the ghost steps between them.
/// <c>Pulse.Lib.CSharp.TopDownRemoveHeap</c>; every member is a <see cref="RegionOpAttribute"/>
/// (a <c>void</c> one is a lemma, called as a ghost statement) except <see cref="Removed"/>.
/// The descent's state is <c>cur</c>, <c>par</c>, <c>gp</c>, the match <c>mt</c> (null until
/// found), its parent <c>pom</c> and <c>found</c>; <c>m0</c> is the loop's measure at the top
/// of the iteration.
/// </summary>
public static class SpecTopDownRemove
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecTopDownRemove is a specification-only construct and has no runtime meaning.");

    /// <summary><paramref name="k0"/> without the element equivalent to <paramref name="k"/>, if any.</summary>
    [SpecOp("Pulse.Lib.CSharp.TopDownRemove.removed")]
    public static Seq<T> Removed<T>(IComparer<T> c, Seq<T> k0, T k) => throw Ghost();

    // What `Node`'s helpers do.

    /// <summary><c>Merge2Nodes</c>, every box where it was.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.merged")]
    public static bool Merged<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? x) where K : class => throw Ghost();

    /// <summary><c>Rotate(rot)</c> from <paramref name="x"/> to the new top <paramref name="y"/>, every box where it was.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rotatedn")]
    public static bool RotatedN<K, T, TRotation>(SpecHeap<K> h0, SpecHeap<K> h1, K? x, K? y, TRotation rot) where K : class => throw Ghost();

    /// <summary><c>Rotate</c>'s single rotations: after the grandchild on side <paramref name="side"/> is blackened.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rot_single")]
    public static void RotSingle<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? x, K? z, bool side) where K : class => throw Ghost();

    /// <summary><c>Rotate</c>'s double rotations.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rot_double")]
    public static void RotDouble<K, T>(SpecHeap<K> h0, K? x, bool side) where K : class => throw Ghost();

    // The descent.

    /// <summary>The loop invariant: a set of <paramref name="k0"/>, and the path to <paramref name="cur"/> is the search for <paramref name="k"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rinvh")]
    public static bool RInv<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? mt, K? pom, bool found) where K : class => throw Ghost();

    /// <summary>The loop's measure: the size of the subtree at <paramref name="cur"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rmeasure")]
    public static SpecInt Measure<K, T>(SpecHeap<K> h, K? root, K? cur) where K : class => throw Ghost();

    /// <summary>After the red sibling is lifted (or with a black one): the parent red, <paramref name="cur"/> a 2-node.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rmidh")]
    public static bool RMid<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? mt, K? pom, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>After the fix-up: <paramref name="cur"/> is not a 2-node.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rfxh")]
    public static bool RFx<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? mt, K? pom, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary><c>ReplaceNode</c>'s precondition: <paramref name="succ"/> and <paramref name="pos"/> are <paramref name="mt"/>'s successor and its parent.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rnpre")]
    public static bool RnPre<K, T>(SpecHeap<K> h, K? root, K? mt, K? pom, K? succ, K? pos) where K : class => throw Ghost();

    /// <summary><c>ReplaceNode</c>'s postcondition: <paramref name="mt"/> is out of the tree, as <c>TopDownSucc.rdel</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rnpost")]
    public static bool RnPost<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, K? root0, K? root1, K? mt) where K : class => throw Ghost();

    /// <summary>The removal at <paramref name="mt"/> removes <paramref name="k"/> from <paramref name="k0"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rpreh")]
    public static bool RPre<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? mt, K? pom, K? succ, K? pos) where K : class => throw Ghost();

    // The ghost steps.

    /// <summary>Before the loop.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_start")]
    public static void Start<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root) where K : class => throw Ghost();

    /// <summary>The top of an iteration: <paramref name="cur"/> can be read; if not a 2-node, nothing to fix.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_at_cur")]
    public static void AtCur<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? mt, K? pom, bool found) where K : class => throw Ghost();

    /// <summary><c>current.ColorRed()</c> at the root.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_fix_root")]
    public static void FixRoot<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, K? root, K? cur, K? par, K? gp, K? mt, K? pom, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary><c>parent.GetSibling(current)</c> can be called.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_sib_pre")]
    public static void SibPre<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? mt, K? pom, bool found) where K : class => throw Ghost();

    /// <summary>The sibling: red under a black parent, or black under a red one.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_at_sib")]
    public static void AtSib<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>The red sibling lifted by a rotation.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.a_mid")]
    public static void AMid<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, bool found) where K : class => throw Ghost();

    /// <summary>Then <c>parent.ColorRed()</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.a_red")]
    public static void ARed<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, SpecHeap<K> h2, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, bool found) where K : class => throw Ghost();

    /// <summary>Then <c>sibling.ColorBlack()</c> and <c>ReplaceChildOrRoot(grandParent, parent, sibling)</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.a_end")]
    public static void AEnd<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, SpecHeap<K> h2, SpecHeap<K> h3, SpecHeap<K> h4, K? root, K? root4, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, bool found) where K : class => throw Ghost();

    /// <summary>The new sibling can be asked for.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_mid_pre")]
    public static void MidPre<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? mt, K? pom, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>The black sibling: a 2-node to merge with, or a red child to rotate up.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_at_mid")]
    public static void AtMid<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary><c>parent.Merge2Nodes()</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_merge")]
    public static void Merge<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary><c>parent.Rotate(parent.GetRotation(current, sibling))</c> to <paramref name="y"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.b_rot")]
    public static void BRot<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, K? y, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>Then <c>newGrandParent.Color = parent.Color</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.b_colw")]
    public static void BColW<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, SpecHeap<K> h2, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, K? y, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>Then <c>parent.ColorBlack()</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.b_blk")]
    public static void BBlk<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, SpecHeap<K> h2, SpecHeap<K> h3, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, K? y, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>Then <c>current.ColorRed()</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.b_cur")]
    public static void BCur<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, SpecHeap<K> h2, SpecHeap<K> h3, SpecHeap<K> h4, K? root, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, K? y, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>Then <c>ReplaceChildOrRoot(grandParent, parent, newGrandParent)</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.b_end")]
    public static void BEnd<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, SpecHeap<K> h1, SpecHeap<K> h2, SpecHeap<K> h3, SpecHeap<K> h4, SpecHeap<K> h5, K? root, K? root5, K? cur, K? par, K? gp, K? mt, K? pom, K? sib, K? y, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>After the fix-up: <paramref name="cur"/> can be read.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_at_fx")]
    public static void AtFx<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? mt, K? pom, bool found, SpecInt m0) where K : class => throw Ghost();

    /// <summary>One step down, by <paramref name="o"/> (<c>-1</c> once found); <paramref name="eq"/> and <paramref name="lt"/> are the tests the body makes of it.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_step")]
    public static void Step<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? cur, K? par, K? mt, K? pom, bool found, SpecInt m0, SpecInt o, bool eq, bool lt) where K : class => throw Ghost();

    /// <summary>After the loop: nothing to remove, or <c>ReplaceNode</c> can be called.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_after")]
    public static void After<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h, K? root, K? par, K? gp, K? mt, K? pom, bool found) where K : class => throw Ghost();

    /// <summary>After <c>ReplaceNode</c>: the tree is a set of the remaining keys.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_replaced")]
    public static void Replaced<K, T>(IComparer<T> c, Seq<T> k0, T k, SpecHeap<K> h0, SpecHeap<K> h1, K? root0, K? root1, K? mt, K? pom, K? succ, K? pos) where K : class => throw Ghost();

    /// <summary><c>root?.ColorBlack()</c> at the end, also when the tree is now empty.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.r_finish")]
    public static void Finish<K, T>(IComparer<T> c, Seq<T> k1, SpecHeap<K> h0, SpecHeap<K> h1, K? root) where K : class => throw Ghost();

    // `ReplaceNode`.

    /// <summary>The facts <c>ReplaceNode</c>'s reads and <c>Debug.Assert</c>s need.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rn_start")]
    public static void RnStart<K, T>(SpecHeap<K> h, K? root, K? mt, K? pom, K? succ, K? pos) where K : class => throw Ghost();

    /// <summary>No successor: <c>match.Left</c> replaces <paramref name="mt"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rn_a")]
    public static void RnA<K, T>(SpecHeap<K> h, K? root, K? mt, K? pom, K? succ, K? pos) where K : class => throw Ghost();

    /// <summary>The successor detached and given <paramref name="mt"/>'s links.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rn_b")]
    public static void RnB<K, T>(SpecHeap<K> h0, SpecHeap<K> h1, SpecHeap<K> h4, K? root, K? mt, K? pom, K? succ, K? pos) where K : class => throw Ghost();

    /// <summary>The colour copied and <c>ReplaceChildOrRoot(parentOfMatch, match, successor)</c>.</summary>
    [RegionOp("Pulse.Lib.CSharp.TopDownRemoveHeap.rn_done")]
    public static void RnDone<K, T>(SpecHeap<K> h0, SpecHeap<K> h4, SpecHeap<K> h5, SpecHeap<K> h6, K? root0, K? root6, K? mt, K? pom, K? succ, K? pos, K? x) where K : class => throw Ghost();
}
