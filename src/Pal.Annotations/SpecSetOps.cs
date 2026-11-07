using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R27.51. Set operations of <c>SortedSet&lt;T&gt;</c> computed by enumerating another set:
/// <c>Pulse.Lib.CSharp.SetOps</c>. A <c>void</c> member is a lemma, called as a ghost
/// statement.
/// </summary>
public static class SpecSetOps
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecSetOps is a specification-only construct and has no runtime meaning.");

    /// <summary>Some element of <paramref name="t"/> is a member of the strictly sorted <paramref name="s"/> under <paramref name="c"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.overlaps")]
    public static bool Overlaps<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: one step of a walk over the suffix <c>t[i..]</c>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.overlaps_step")]
    public static void OverlapsStep<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i) => throw Ghost();

    /// <summary>A lemma: the whole of <paramref name="t"/> is its suffix from 0.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.overlaps_whole")]
    public static void OverlapsWhole<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: two strictly sorted sequences in disjoint ranges do not overlap.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.overlaps_disjoint")]
    public static void OverlapsDisjoint<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();
}
