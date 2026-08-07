using System;
using PalLang;

// §12. A doubly linked list, specified by *list segments*.
//
// This is the case §10's `[Model]` scheme cannot reach. §10 derives a class's ownership
// predicate from one downward fold over one recursive field. A segment is bounded at both
// ends, so it carries two boundary pointers no fold over the fields could produce; its
// empty case is `from == to_`, a relation between two of those boundaries rather than a
// property of one; and its central lemma -- that two adjacent segments compose -- relates
// two instances of the predicate at once.
//
// So the predicate is the user's. `DNode` below is `[Plain]`: the translator emits its
// representation and stops. Everything else -- the predicate, its intro and elim lemmas,
// and the segment-append lemma -- lives in `DllSeg.fst` beside this file, and is named
// from C# by the declarations below.
//
// R12.6. The Pulse is in a *file*, not a string literal: `[IncludePulseFile]` reads it and
// emits it verbatim as a module whose name is the file's base name, so an editor,
// `fstar.exe` and the IDE all see real F* and the module name cannot drift from the
// `module` header the file already carries.
//
// Pinned first, and independently, by test/pulse_facts/SegmentFacts.fst.
[assembly: IncludePulseFile("DllSeg.fst")]

namespace PalCSharp.Tests;

/// <summary>
/// R12.1. A <c>[Plain]</c> class: the translator emits the record, the reference and the
/// nullable reference, and derives nothing else. There is no <c>[Model]</c> because there
/// is no abstraction function -- what a `DNode` means is only ever said by a predicate
/// that ranges over many of them at once.
/// </summary>
[Plain]
public sealed class DNode
{
    internal int value;
    internal DNode? prev;
    internal DNode? next;
}

/// <summary>
/// R12.2. The C# face of the user's predicate. An <c>SlProp</c>-valued <c>[SpecOp]</c> is
/// an *ownership* clause: where it appears in a <c>[Requires]</c> or <c>[Ensures]</c> it
/// joins the separating conjunction rather than the <c>pure</c>.
/// </summary>
public static class Dll
{
    /// <summary>The nodes from <paramref name="from"/> to <paramref name="last"/>.</summary>
    [SpecOp("DllSeg.seg")]
    public static SlProp Seg(DNode? from, DNode? prev, DNode? to, DNode? last,
                             SpecList<SpecInt> values) => throw new InvalidOperationException();

    /// <summary>A whole list: the segment that runs off both ends.</summary>
    [SpecOp("DllSeg.whole")]
    public static SlProp Whole(DNode? head, DNode? tail, SpecList<SpecInt> values)
        => throw new InvalidOperationException();

    /// <summary>
    /// <see cref="Seg"/> with its first node unfolded. The node is named once: R10.2 makes
    /// <c>DNode</c> and <c>DNode?</c> one Pulse type, so the cursor the contract talks about
    /// is already the reference a field access reads through.
    /// </summary>
    [SpecOp("DllSeg.opened")]
    public static SlProp Opened(DNode? from, DNode? prev, DNode? to, DNode? last,
                                SpecList<SpecInt> values) => throw new InvalidOperationException();

    /// <summary>The ownership a freshly allocated node has: its three field values.</summary>
    [SpecOp("DllSeg.cell")]
    public static SlProp Cell(DNode? node, SpecInt value, DNode? prev, DNode? next)
        => throw new InvalidOperationException();
}

/// <summary>
/// R12.7. The proof steps, as C# methods. A <c>[Lemma]</c> whose contract mentions an
/// <c>SlProp</c> is emitted as a Pulse <c>ghost fn</c> rather than an F* <c>Lemma</c>,
/// because a <c>Lemma</c> cannot carry ownership; the test is the same one R12.2 already
/// applies to a method's clauses, so nothing new has to be declared. Each of these is
/// erased by <c>[Conditional("PAL")]</c>, so a caller pays nothing at run time.
///
/// <para>The style rule §12 sets is visible here: <em>one lemma per step a C# body
/// takes</em>, with a signature over parameters, locals, <c>null</c> and spec lists, and
/// with every <c>with</c> and every <c>rewrite</c> the step needs kept inside
/// <c>DllSeg.fst</c>. A body that has to name a Pulse existential to make its next step
/// go through is a signal that the predicate library is missing a lemma — not a licence
/// to write raw Pulse at the call site.</para>
/// </summary>
public static class DllProof
{
    /// <summary>
    /// A segment is empty exactly when its cursor is null — <em>only</em> when the right
    /// boundary is the end of the list. For a general segment emptiness is
    /// <c>from == to</c>, so this is a fact about the user's predicate and not about C#'s
    /// null test, which is why it must be stated and proved rather than assumed.
    /// </summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("DllSeg.dll_cases 1.0R $(from) $(prev) $(last) #$(values)")]
    [Preserves("Dll.Seg(from, prev, null, last, values)")]
    [Ensures("Pal.Iff(from != null, !values.IsEmpty)")]
    public static void Cases(DNode? from, DNode? prev, DNode? last,
                             Ghost<SpecList<SpecInt>> values) { }

    /// <summary>Open the first node of a non-empty segment.</summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("DllSeg.seg_open $(from) $(prev) $(to) $(last) $(values)")]
    [Requires("Dll.Seg(from, prev, to, last, values)")]
    [Requires("!values.IsEmpty")]
    [Ensures("Dll.Opened(from, prev, to, last, values)")]
    public static void Open(DNode? from, DNode? prev, DNode? to, DNode? last,
                            Ghost<SpecList<SpecInt>> values) { }

    /// <summary>Close it again, at whatever left boundary its <c>prev</c> field now holds.</summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("DllSeg.seg_close $(from) $(prev) $(to) $(last) $(values)")]
    [Requires("Dll.Opened(from, prev, to, last, values)")]
    [Ensures("Dll.Seg(from, prev, to, last, values)")]
    public static void Close(DNode? from, DNode? prev, DNode? to, DNode? last,
                             Ghost<SpecList<SpecInt>> values) { }

    /// <summary>Push a node the caller owns outright onto the front of a segment.</summary>
    [Lemma, System.Diagnostics.Conditional("PAL")]
    [PulseBody("DllSeg.seg_cons $(node) $(value) $(prev) $(next) $(to) $(last) $(values)")]
    [Requires("Dll.Cell(node, value, prev, next)")]
    [Requires("Dll.Seg(next, node, to, last, values)")]
    [Ensures("Dll.Seg(node, prev, to, last, SpecList.Cons(value, values))")]
    public static void Cons(DNode? node, SpecInt value, DNode? prev, DNode? next, DNode? to,
                            DNode? last, Ghost<SpecList<SpecInt>> values) { }
}
