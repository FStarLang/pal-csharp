using System;
using PalLang;

// §16. A **cursor**: iterative traversal of a linked structure.
//
// This is the case §10.7 recorded as out of reach and §15.5 repeated. §10 derives a class's
// ownership predicate from one downward fold over one recursive field, so what a client
// holds is always "the chain from here to the end". A loop that advances a cursor through
// that chain has nowhere to put the part it has already walked, and R10.7's window -- opened
// at a null test, closed at the end of the branch -- is exactly the shape of a *recursive*
// traversal and exactly not an iterative one. Every operation in `test/generic_list` is
// recursive for that reason and no other.
//
// §12 is the answer: a *list segment*, bounded at both ends, so that the prefix already
// walked is one instance of the predicate and the suffix still to walk is another. A segment
// carries two boundary pointers no fold over the fields could produce and its empty case is
// a relation between them, so it cannot be derived -- it is the user's, and lives in
// `CellSeg.fst` beside this file.
//
// Two rules make the loop itself work, and neither is about linked lists:
//
//   * R5.8c -- a `Pal.Invariant` clause may be an `SlProp`, in which case it joins the
//     invariant's separating conjunction rather than its `pure`. Without it a loop can only
//     ever state facts about *values*, and a loop that owns a changing part of the heap
//     cannot be specified at all.
//   * R12.7b -- a `[Lemma]` emitted as a Pulse `ghost fn` has its pure postcondition guarded
//     by its pure precondition, exactly as R4.8 already does for a method. `Advance` below
//     reports `xs[i]`, which is ill-typed until `i < xs.Length` is a hypothesis.
//
// The design decision the whole file turns on is the *shape of the invariant*. A pal-csharp
// loop invariant existentially quantifies the mutable locals and nothing else (R5.8), so the
// contents of the two segments have to be functions of a mutable local. They are: the
// counter. The prefix is `SpecList.Take(xs, i)` and the suffix is `SpecList.Drop(xs, i)`.
// That is not a contrivance to fit the rule -- it is the invariant a person writes by hand --
// but it does mean a cursor needs no new loop machinery beyond R5.8c.
//
// Pinned first, and independently, by test/pulse_facts/CursorFacts.fst.
[assembly: IncludePulseFile("CellSeg.fst")]

namespace PalCSharp.Tests;

/// <summary>
/// R12.1 + R15.1. A <c>[Plain]</c> class that is also generic: the translator emits the
/// record, the reference and the nullable reference, all as functions of <c>T</c>, and
/// derives nothing else. There is no <c>[Model]</c> because there is no abstraction function
/// — what a <c>Cell&lt;T&gt;</c> means is only ever said by a predicate that ranges over many
/// of them at once, and says *which* ones.
/// </summary>
[Plain]
public sealed class Cell<T>
{
    // Every `Cell<T>` in this directory is built by an object initializer, which is what
    // R12.4 translates; the `= default!` is what tells a nullable-aware C# build so, since
    // an unconstrained `T` has no null to fall back on. It costs the translation nothing —
    // R12.1 reads the field's name and type and nothing else.
    internal T value = default!;
    internal Cell<T>? next;
}

/// <summary>
/// R12.2. The C# face of the user's predicate. An <c>SlProp</c>-valued <c>[SpecOp]</c> is an
/// *ownership* clause: where it appears in a <c>[Requires]</c>, an <c>[Ensures]</c> or — this
/// is what R5.8c adds — a <c>Pal.Invariant</c>, it joins the separating conjunction rather
/// than the <c>pure</c>.
/// </summary>
public static class Chain
{
    /// <summary>The cells from <paramref name="from"/> up to but not including
    /// <paramref name="to"/>, holding <paramref name="values"/>.</summary>
    [SpecOp("CellSeg.seg")]
    public static SlProp Seg<T>(Cell<T>? from, Cell<T>? to, SpecList<T> values)
        => throw new InvalidOperationException();

    /// <summary>
    /// A whole chain: the segment that ends at <c>null</c>. Saying it this way rather than as
    /// a second predicate is what lets a cursor's prefix and its suffix be *the same*
    /// predicate, which is what makes <see cref="ChainProof.Advance"/> a statement about one
    /// thing rather than two.
    /// </summary>
    [SpecOp("CellSeg.whole")]
    public static SlProp Whole<T>(Cell<T>? from, SpecList<T> values)
        => throw new InvalidOperationException();

    /// <summary>
    /// <see cref="Seg"/> with its first cell unfolded, its two field values still unknown.
    /// This is what an elimination lemma can promise: a C# <c>[Ensures]</c> has no way to
    /// bind an existential, and the values in a cell are not determined by the list — the
    /// <c>next</c> field is a pointer, and no specification of the contents mentions it.
    /// </summary>
    [SpecOp("CellSeg.opened_some")]
    public static SlProp Opened<T>(Cell<T>? from, Cell<T>? to, SpecList<T> values)
        => throw new InvalidOperationException();

    /// <summary>
    /// <see cref="Opened"/> with the two field values named. This is the form the *step*
    /// needs: the new split point is the <c>next</c> field, a value that exists only once the
    /// heap has been read, which is what an iterative walk needs and a recursive one does
    /// not. A C# body reaches it the only way it can — by reading the fields — and then names
    /// the locals it read into.
    /// </summary>
    /// <summary>The ownership a freshly allocated cell has: its two field values.</summary>
    [SpecOp("CellSeg.held")]
    public static SlProp Held<T>(Cell<T>? cell, T value, Cell<T>? next)
        => throw new InvalidOperationException();

    [SpecOp("CellSeg.opened")]
    public static SlProp OpenedAt<T>(Cell<T>? from, T value, Cell<T>? next,
                                     Cell<T>? to, SpecList<T> values)
        => throw new InvalidOperationException();
}

/// <summary>
/// R12.7. The proof steps, as C# methods — one lemma per step a C# loop takes. A
/// <c>[Lemma]</c> whose contract mentions an <c>SlProp</c> is emitted as a Pulse
/// <c>ghost fn</c> rather than an F* <c>Lemma</c>, because a <c>Lemma</c> cannot carry
/// ownership. Each is erased by <c>[Conditional("PAL")]</c>, so a caller pays nothing.
///
/// <para>Read the six together and they are the anatomy of a walk: <c>Start</c> opens it,
/// <c>AtEnd</c> is its loop condition, <c>Open</c>/<c>Advance</c> are its body, and
/// <c>Close</c>/<c>Finish</c> end it — early or at the end. Every <c>with</c> and every
/// <c>rewrite</c> each step needs stays inside <c>CellSeg.fst</c>, so a walk written in C#
/// contains no raw Pulse at all.</para>
/// </summary>
public static class ChainProof
{
    /// <summary>
    /// Begin the walk. <c>Take(xs, 0)</c> is empty and <c>Drop(xs, 0)</c> is everything, so
    /// the loop is entered with the cursor at the head and the counter at zero and the
    /// invariant holds by construction.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("CellSeg.seg_start $(head) $(xs)")]
    [Requires("Chain.Whole(head, xs)")]
    [Ensures("Chain.Seg(head, head, SpecList.Take(xs, 0))")]
    [Ensures("Chain.Whole(head, SpecList.Drop(xs, 0))")]
    public static void Start<T>(Cell<T>? head, Ghost<SpecList<T>> xs) { }

    /// <summary>
    /// Push a cell the caller owns outright onto the front of a chain. This is the one step
    /// that *builds* rather than walks, and it is here because a walk needs something to
    /// walk: it is also the only place a <c>[Plain]</c> allocation meets the predicate.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("CellSeg.seg_push $(cell) $(value) $(next) $(xs)")]
    [Requires("Chain.Held(cell, value, next)")]
    [Requires("Chain.Whole(next, xs)")]
    [Ensures("Chain.Whole(cell, SpecList.Cons(value, xs))")]
    public static void Push<T>(Cell<T>? cell, T value, Cell<T>? next, Ghost<SpecList<T>> xs) { }

    /// <summary>
    /// The loop condition, stated once so that no C# body has to reason about it. The null
    /// test is a statement about the *list*, and for a segment that is a fact about the
    /// user's predicate rather than about C#'s <c>null</c>, which is why it must be proved.
    /// The counter half is what an invariant indexed by <c>Take</c>/<c>Drop</c> needs.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("CellSeg.seg_at_end $(from) $(i) $(xs)")]
    [Preserves("Chain.Whole(from, SpecList.Drop(xs, i))")]
    [Requires("0 <= i && i <= xs.Length")]
    [Ensures("Pal.Iff(from == null, i == xs.Length)")]
    [Ensures("Pal.Iff(from != null, !SpecList.Drop(xs, i).IsEmpty)")]
    public static void AtEnd<T>(Cell<T>? from, SpecInt i, Ghost<SpecList<T>> xs) { }

    /// <summary>
    /// Open the first cell of a non-empty suffix, so that its two fields can be read. The
    /// cursor is named once: R10.2 makes <c>Cell&lt;T&gt;</c> and <c>Cell&lt;T&gt;?</c> one
    /// Pulse type, so the reference a field access reads through is the cursor itself.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("CellSeg.seg_open $(from) $(rest)")]
    [Requires("Chain.Whole(from, rest)")]
    [Requires("!rest.IsEmpty")]
    [Ensures("Chain.Opened(from, null, rest)")]
    public static void Open<T>(Cell<T>? from, Ghost<SpecList<T>> rest) { }

    /// <summary>
    /// The step: move the split point one cell to the right. The cell just opened is
    /// appended to the prefix and taken off the front of the suffix — <c>snoc</c> on one and
    /// <c>tail</c> on the other, at once.
    ///
    /// <para>Both halves are <c>Take</c>/<c>Drop</c> of the counter, so the caller never has
    /// to name either list — it names <c>i</c>, and the predicate says the rest. The
    /// postcondition also reports what was read, which is how a C# body learns that the value
    /// it just took out of the cell is element <c>i</c> of the list it was given. That
    /// clause is exactly why R12.7b is needed: <c>xs[i]</c> is ill-typed until
    /// <c>i &lt; xs.Length</c> is a hypothesis.</para>
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("CellSeg.seg_advance $(head) $(from) $(value) $(next) $(i) $(xs)")]
    [Requires("Chain.Seg(head, from, SpecList.Take(xs, i))")]
    [Requires("Chain.OpenedAt(from, value, next, null, SpecList.Drop(xs, i))")]
    [Requires("0 <= i && i < xs.Length")]
    [Ensures("Chain.Seg(head, next, SpecList.Take(xs, i + 1))")]
    [Ensures("Chain.Whole(next, SpecList.Drop(xs, i + 1))")]
    [Ensures("Pal.Same(value, xs[i])")]
    public static void Advance<T>(Cell<T>? head, Cell<T>? from, T value,
                                  Cell<T>? next, SpecInt i, Ghost<SpecList<T>> xs) { }

    /// <summary>
    /// Give the chain back from wherever the cursor happens to be. This is what a C#
    /// <c>return</c> from inside the walk costs — one lemma call, because the two halves
    /// compose at any split point and not only at the end.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("CellSeg.seg_close $(head) $(from) $(i) $(xs)")]
    [Requires("Chain.Seg(head, from, SpecList.Take(xs, i))")]
    [Requires("Chain.Whole(from, SpecList.Drop(xs, i))")]
    [Ensures("Chain.Whole(head, xs)")]
    public static void Close<T>(Cell<T>? head, Cell<T>? from, SpecInt i,
                                Ghost<SpecList<T>> xs) { }

    /// <summary>
    /// Reaching <c>null</c> ends the walk: the counter has arrived at the length, and the
    /// chain comes back whole. <see cref="Close"/> plus <see cref="AtEnd"/>, named once so
    /// that the ordinary exit is one call rather than two.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("CellSeg.seg_finish $(head) $(from) $(i) $(xs)")]
    [Requires("Chain.Seg(head, from, SpecList.Take(xs, i))")]
    [Requires("Chain.Whole(from, SpecList.Drop(xs, i))")]
    [Requires("0 <= i && i <= xs.Length && from == null")]
    [Ensures("Chain.Whole(head, xs)")]
    [Ensures("i == xs.Length")]
    public static void Finish<T>(Cell<T>? head, Cell<T>? from, SpecInt i,
                                 Ghost<SpecList<T>> xs) { }
}
