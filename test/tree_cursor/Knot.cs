using System;
using PalLang;

// §16 at the branching case: a **descent**, i.e. an iterative walk down a search tree.
//
// `test/list_cursor` established the shape. What is walked is bounded at both ends by a
// user-written predicate (§12), the two halves are functions of the loop counter (R5.8),
// an `SlProp`-valued `Pal.Invariant` clause carries the ownership (R5.8c), and every
// `with`/`rewrite` the proof needs stays inside the user's Pulse file. Nothing about that
// was about lists, and this directory is the demonstration: the predicate here is a
// one-hole *context* rather than a segment, and not one translator rule changed.
//
// Three things are genuinely new, and only the third is about trees.
//
//   * **The walked part is a spine.** `KnotPath.knot_path` owns the path from the root down
//     to the cursor together with every sibling subtree it passed, and `plug` fills the hole
//     back in. `path_close` is `seg_close`; `plug` is `Append`.
//
//   * **The counter still indexes it.** A descent's context is path-dependent, so nothing
//     like `Take` works -- but the path a *search* takes is determined by the tree and the
//     key, both fixed for the whole loop. So `Ctx(t, key, n)` and `Sub(t, key, n)` are
//     functions of the counter exactly as `Take(xs, i)` and `Drop(xs, i)` are, and R5.8's
//     "the invariant quantifies the mutable locals and nothing else" is satisfied without
//     any new machinery.
//
//   * **The loop has two exits.** A chain walk ends when the cursor is null; a search ends
//     when the cursor is null *or* when the key is found. A C# `break` would be R5.10
//     territory, so `Search.Find` does not use one: an `int` flag `live` is the loop
//     condition and the measure is `Sub(t, key, n).Size + live`, which falls on a descent
//     (the subtree shrinks) and falls on a stop (the flag does). That device is not about
//     trees at all -- it is how any pal-csharp loop leaves early.
//
// Pinned first, and independently, by test/pulse_facts/TreeCursorFacts.fst.
[assembly: IncludePulseFile("KnotPath.fst")]

namespace PalCSharp.Tests;

/// <summary>
/// R12.1 + R15.1 at four fields, two of them recursive. The translator emits the record,
/// the reference and the nullable reference as functions of <c>T</c>, and derives nothing
/// else — which is why a second recursive field costs it nothing.
///
/// <para>The order is <c>Kv</c>-style: an <c>int</c> key beside the payload, because R15.4
/// refuses a constrained type parameter and so <c>where T : IComparable&lt;T&gt;</c> is not
/// available to say what order a search tree is in. A tree ordered by arithmetic is the
/// specifiable half of the two.</para>
/// </summary>
[Plain]
public sealed class Knot<T>
{
    // The declaration order is the record's field order, and `KnotPath.fst` writes its
    // literals in it. `= default!` is what tells a nullable-aware C# build that an
    // unconstrained `T` has no null to fall back on; it costs the translation nothing.
    internal int key;
    internal T value = default!;
    internal Knot<T>? left;
    internal Knot<T>? right;
}

/// <summary>
/// R11.1 + R11.2. The spec-level half of the descent: the one-hole context type and the two
/// functions that index it by the counter. Nothing here is known to the translator — every
/// member names an F* term in <c>KnotPath.fst</c> and the emitter writes that name out.
/// </summary>
[SpecType("KnotPath.frame")]
public readonly struct SpecFrame<T>
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecFrame<T> is a specification-only construct and has no runtime meaning.");

    public static bool operator ==(SpecFrame<T> a, SpecFrame<T> b) => throw Ghost();
    public static bool operator !=(SpecFrame<T> a, SpecFrame<T> b) => throw Ghost();

    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

/// <summary>
/// R12.2. The C# face of the user's predicate. An <c>SlProp</c>-valued <c>[SpecOp]</c> is an
/// ownership clause wherever it appears — in a <c>[Requires]</c>, an <c>[Ensures]</c> or a
/// <c>Pal.Invariant</c> (R5.8c).
/// </summary>
public static class Descent
{
    private static Exception Ghost() => new InvalidOperationException(
        "Descent is a specification-only construct and has no runtime meaning.");

    // R11.3. `Descent` is `SpecFrame<T>`'s companion: it declares the frame constructors,
    // which is what makes it the class the frame operations below belong to. The two
    // constructors are also the whole content of "a frame is a node with one child missing":
    // the sibling subtree that was *not* descended into is owned in the frame, which is why
    // the spine can be given back at the end without having been copied.

    /// <summary>A step that went left, keeping the entry and the right subtree.</summary>
    [SpecCtor("KnotPath.FLeft")]
    public static SpecFrame<T> WentLeft<T>(SpecKv<T> entry, SpecTree<SpecKv<T>> right)
        => throw Ghost();

    /// <summary>A step that went right, keeping the left subtree and the entry.</summary>
    [SpecCtor("KnotPath.FRight")]
    public static SpecFrame<T> WentRight<T>(SpecTree<SpecKv<T>> left, SpecKv<T> entry)
        => throw Ghost();

    /// <summary>The whole tree rooted at <paramref name="from"/>.</summary>
    [SpecOp("KnotPath.holds")]
    public static SlProp Holds<T>(Knot<T>? from, SpecTree<SpecKv<T>> tree) => throw Ghost();

    /// <summary>
    /// The spine from <paramref name="from"/> down to <paramref name="to"/>, with every
    /// sibling subtree it passed. This is what a segment is to a chain, and like a segment
    /// its empty case relates its two boundary references — which is exactly the clause no
    /// derived <c>[Model]</c> invariant could ever have.
    /// </summary>
    [SpecOp("KnotPath.spine")]
    public static SlProp Spine<T>(Knot<T>? from, Knot<T>? to, SpecList<SpecFrame<T>> context)
        => throw Ghost();

    /// <summary>The ownership a freshly allocated node has: its four field values.</summary>
    [SpecOp("KnotPath.knot_held")]
    public static SlProp Held<T>(Knot<T> node, SpecInt key, T value, Knot<T>? left, Knot<T>? right)
        => throw Ghost();

    /// <summary>
    /// <see cref="Holds"/> with the node at the cursor unfolded, its four field values still
    /// unknown. This is what an elimination lemma can promise, because a C# postcondition
    /// cannot bind an existential and the body is about to produce the four by *reading the
    /// fields*.
    /// </summary>
    [SpecOp("KnotPath.knot_open_some")]
    public static SlProp Opened<T>(Knot<T>? from, Knot<T> node, SpecTree<SpecKv<T>> sub)
        => throw Ghost();

    /// <summary>
    /// <see cref="Opened"/> with the four field values named — the form each step takes,
    /// because the new cursor is a field, a value that exists only once the heap has been
    /// read.
    /// </summary>
    [SpecOp("KnotPath.knot_opened")]
    public static SlProp OpenedAt<T>(Knot<T>? from, Knot<T> node, T value,
                                     Knot<T>? left, Knot<T>? right, SpecTree<SpecKv<T>> sub)
        => throw Ghost();

    /// <summary>
    /// The key at the root of a subtree, read off the model. This is how a step says which
    /// way it went without naming a machine integer, which R4.13 gives a C# contract no way
    /// to write: the guard is <c>key &lt; NodeKey(Sub(t, key, n))</c>, and the C# body's own
    /// <c>key &lt; nk</c> implies it because <see cref="OpenedAt"/> ties the field to the
    /// model.
    /// </summary>
    [SpecOp("KnotPath.node_key")]
    public static SpecInt NodeKey<T>(SpecTree<SpecKv<T>> sub) => throw Ghost();

    /// <summary>
    /// The subtree still to be searched after <paramref name="steps"/> steps of looking for
    /// <paramref name="key"/>. <c>Drop</c>, for a descent.
    /// </summary>
    [SpecOp("KnotPath.dsub")]
    public static SpecTree<SpecKv<T>> Sub<T>(SpecTree<SpecKv<T>> tree, SpecInt key, SpecInt steps)
        => throw Ghost();

    /// <summary>The spine walked in those steps, outermost first. <c>Take</c>, for a
    /// descent.</summary>
    [SpecOp("KnotPath.dctx")]
    public static SpecList<SpecFrame<T>> Ctx<T>(SpecTree<SpecKv<T>> tree, SpecInt key,
                                                SpecInt steps)
        => throw Ghost();
}

/// <summary>
/// R12.7. The proof steps, as C# methods. A <c>[Lemma]</c> whose contract mentions an
/// <c>SlProp</c> is emitted as a Pulse <c>ghost fn</c> rather than an F* <c>Lemma</c>,
/// because a <c>Lemma</c> cannot carry ownership; <c>[Conditional("PAL")]</c> erases every
/// call, so a stock build pays nothing.
///
/// <para>Read them in order and they are the anatomy of a search: <see cref="Start"/> opens
/// it, <see cref="AtEnd"/> is its loop condition, <see cref="Open"/> is its read,
/// <see cref="Found"/>/<see cref="Left"/>/<see cref="Right"/> are its three outcomes, and
/// <see cref="Close"/> ends it from wherever it stopped. <see cref="Empty"/> and
/// <see cref="Node"/> are the two that build rather than walk.</para>
/// </summary>
public static class DescentProof
{
    /// <summary>A null reference denotes the empty tree. Which constructor null denotes is
    /// the one thing a predicate's author must say, so they say it.</summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_empty #$(T) ()")]
    [Ensures("Descent.Holds<T>(null, SpecTree.Leaf<SpecKv<T>>())")]
    public static void Empty<T>() { }

    /// <summary>
    /// Assemble a node from two trees the caller owns outright. This is the only place a
    /// <c>[Plain]</c> allocation meets the predicate, and the only thing a test needs in
    /// order to have something to descend through.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_node $(node) $(key) $(value) $(left) $(right) $(lt) $(rt)")]
    [Requires("Descent.Held(node, key, value, left, right)")]
    [Requires("Descent.Holds(left, lt)")]
    [Requires("Descent.Holds(right, rt)")]
    [Ensures("Descent.Holds(node, SpecTree.Branch(lt, SpecTree.Entry(key, value), rt))")]
    public static void Node<T>(Knot<T> node, SpecInt key, T value, Knot<T>? left, Knot<T>? right,
                               Ghost<SpecTree<SpecKv<T>>> lt, Ghost<SpecTree<SpecKv<T>>> rt) { }

    /// <summary>
    /// Begin the descent. <c>Ctx(t, key, 0)</c> is empty and <c>Sub(t, key, 0)</c> is the
    /// whole tree, so the loop is entered with the cursor at the root and the counter at
    /// zero and the invariant holds by construction.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_start $(root) $(key) $(tree)")]
    [Requires("Descent.Holds(root, tree)")]
    [Ensures("Descent.Spine(root, root, Descent.Ctx(tree, key, 0))")]
    [Ensures("Descent.Holds(root, Descent.Sub(tree, key, 0))")]
    public static void Start<T>(Knot<T>? root, SpecInt key, Ghost<SpecTree<SpecKv<T>>> tree) { }

    /// <summary>
    /// The loop condition, and the answer at the bottom. A null cursor means the remaining
    /// subtree is a leaf, and a leaf means the key is not in the tree at all — which is why
    /// the branch that stops there may simply keep the fallback.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_at_end $(from) $(key) $(steps) $(tree)")]
    [Preserves("Descent.Holds(from, Descent.Sub(tree, key, steps))")]
    [Ensures("Pal.Iff(from == null, Descent.Sub(tree, key, steps).IsLeaf)")]
    [Ensures("Pal.Implies(from == null, !SpecTree.HasKey(tree, key))")]
    public static void AtEnd<T>(Knot<T>? from, SpecInt key, SpecInt steps,
                                Ghost<SpecTree<SpecKv<T>>> tree) { }

    /// <summary>
    /// A key the map does not hold reads back as the fallback. This one owns nothing and
    /// mentions no cursor: it is a fact about the model alone, which is why a caller that
    /// only wants membership (<c>SearchVariant.Contains</c>) never has to name a fallback
    /// value at all, while one that wants the value calls this once at the bottom.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.kget_absent $(tree) $(key) $(fallback)")]
    [Requires("!SpecTree.HasKey(tree, key)")]
    [Ensures("Pal.Same(SpecTree.Get(tree, key, fallback), fallback)")]
    public static void Absent<T>(SpecInt key, T fallback,
                                 Ghost<SpecTree<SpecKv<T>>> tree) { }

    /// <summary>
    /// Open the node at the cursor so that its four fields can be read.
    /// <paramref name="from"/> and <paramref name="node"/> are the same node named twice —
    /// once as the nullable cursor the invariant talks about, once as the reference a field
    /// access reads through (R10.2c).
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_open $(from) $(node) $(sub)")]
    [Requires("Descent.Holds(from, sub)")]
    [Requires("!sub.IsLeaf && from == node")]
    [Ensures("Descent.Opened(from, node, sub)")]
    public static void Open<T>(Knot<T>? from, Knot<T> node, Ghost<SpecTree<SpecKv<T>>> sub) { }

    /// <summary>
    /// The hit: the node at the cursor carries the key, so the value read out of it is the
    /// answer. The node is closed straight back up, because a hit ends the descent and the
    /// spine is still exactly <c>Ctx(t, key, n)</c>.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_found $(from) $(node) $(value) $(left) $(right) " +
               "$(key) $(steps) $(fallback) $(tree)")]
    [Requires("Descent.OpenedAt(from, node, value, left, right, " +
              "Descent.Sub(tree, key, steps))")]
    [Requires("key == Descent.NodeKey(Descent.Sub(tree, key, steps))")]
    [Ensures("Descent.Holds(from, Descent.Sub(tree, key, steps))")]
    [Ensures("Pal.Same(SpecTree.Get(tree, key, fallback), value)")]
    [Ensures("SpecTree.HasKey(tree, key)")]
    public static void Found<T>(Knot<T>? from, Knot<T> node, T value,
                                Knot<T>? left, Knot<T>? right,
                                SpecInt key, SpecInt steps, T fallback,
                                Ghost<SpecTree<SpecKv<T>>> tree) { }

    /// <summary>
    /// The step to the left child: the node at the cursor joins the spine, the cursor moves
    /// down, and the counter's two indices move with it. The postcondition also reports that
    /// the remaining subtree got strictly smaller, which is what the loop's
    /// <c>Pal.Decreases</c> needs — a tree has no length, so a counter alone cannot bound it.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_left $(root) $(from) $(node) $(value) $(left) " +
               "$(right) $(key) $(steps) $(tree)")]
    [Requires("Descent.Spine(root, from, Descent.Ctx(tree, key, steps))")]
    [Requires("Descent.OpenedAt(from, node, value, left, right, " +
              "Descent.Sub(tree, key, steps))")]
    [Requires("0 <= steps && key < Descent.NodeKey(Descent.Sub(tree, key, steps))")]
    [Ensures("Descent.Spine(root, left, Descent.Ctx(tree, key, steps + 1))")]
    [Ensures("Descent.Holds(left, Descent.Sub(tree, key, steps + 1))")]
    [Ensures("Descent.Sub(tree, key, steps + 1).Size < Descent.Sub(tree, key, steps).Size")]
    public static void Left<T>(Knot<T>? root, Knot<T>? from, Knot<T> node, T value,
                               Knot<T>? left, Knot<T>? right, SpecInt key, SpecInt steps,
                               Ghost<SpecTree<SpecKv<T>>> tree) { }

    /// <summary>The step to the right child.</summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_right $(root) $(from) $(node) $(value) $(left) " +
               "$(right) $(key) $(steps) $(tree)")]
    [Requires("Descent.Spine(root, from, Descent.Ctx(tree, key, steps))")]
    [Requires("Descent.OpenedAt(from, node, value, left, right, " +
              "Descent.Sub(tree, key, steps))")]
    [Requires("0 <= steps && key > Descent.NodeKey(Descent.Sub(tree, key, steps))")]
    [Ensures("Descent.Spine(root, right, Descent.Ctx(tree, key, steps + 1))")]
    [Ensures("Descent.Holds(right, Descent.Sub(tree, key, steps + 1))")]
    [Ensures("Descent.Sub(tree, key, steps + 1).Size < Descent.Sub(tree, key, steps).Size")]
    public static void Right<T>(Knot<T>? root, Knot<T>? from, Knot<T> node, T value,
                                Knot<T>? left, Knot<T>? right, SpecInt key, SpecInt steps,
                                Ghost<SpecTree<SpecKv<T>>> tree) { }

    /// <summary>
    /// Give the tree back from wherever the descent stopped. One lemma call, at the bottom
    /// or on a hit alike, because the spine and the remaining subtree compose at every point
    /// on the path and not only at the end.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("KnotPath.tree_close $(root) $(from) $(key) $(steps) $(tree)")]
    [Requires("Descent.Spine(root, from, Descent.Ctx(tree, key, steps))")]
    [Requires("Descent.Holds(from, Descent.Sub(tree, key, steps))")]
    [Ensures("Descent.Holds(root, tree)")]
    public static void Close<T>(Knot<T>? root, Knot<T>? from, SpecInt key, SpecInt steps,
                                Ghost<SpecTree<SpecKv<T>>> tree) { }
}
