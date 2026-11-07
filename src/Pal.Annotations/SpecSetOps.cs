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

    /// <summary><paramref name="s"/> after removing each element of <paramref name="t"/>, first to last (<c>ExceptWith</c>).</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.except")]
    public static Seq<T> Except<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: removing <c>t[i]</c> extends the prefix <c>t[0..i)</c> by one.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.except_step")]
    public static void ExceptStep<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i) => throw Ghost();

    /// <summary>A lemma: the whole of <paramref name="t"/> is its prefix of its length.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.except_whole")]
    public static void ExceptWhole<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: <c>t[i]</c> outside the range of the strictly sorted <paramref name="s"/> removes nothing.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.except_skip")]
    public static void ExceptSkip<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i) => throw Ghost();

    /// <summary>A lemma: past the range of <paramref name="s"/>, the rest of a strictly sorted <paramref name="t"/> removes nothing.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.except_break")]
    public static void ExceptBreak<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i) => throw Ghost();

    /// <summary>A lemma: when the ranges of two strictly sorted sequences are disjoint, nothing is removed.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.except_disjoint")]
    public static void ExceptDisjoint<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary><paramref name="s"/> after, for each element of <paramref name="t"/> first to last, removing it if it is a member and inserting it if not (<c>SymmetricExceptWith</c>).</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.sym_except")]
    public static Seq<T> SymmetricExcept<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: flipping <c>t[i]</c> extends the prefix <c>t[0..i)</c> by one.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.sym_except_step")]
    public static void SymmetricExceptStep<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i) => throw Ghost();

    /// <summary>A lemma: the whole of <paramref name="t"/> is its prefix of its length.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.sym_except_whole")]
    public static void SymmetricExceptWhole<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: flipping the first <paramref name="i"/> elements of <paramref name="t"/> adds at most <paramref name="i"/> elements.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetOps.sym_except_length")]
    public static void SymmetricExceptLength<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i) => throw Ghost();
}
