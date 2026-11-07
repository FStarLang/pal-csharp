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

    /// <summary>The merge of <paramref name="s"/> and <paramref name="t"/>, in order; of two elements that compare equal, the one of <paramref name="t"/> (<c>UnionWith</c>'s merge).</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.union")]
    public static Seq<T> Union<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: one step of the merge, over the suffixes from <paramref name="i"/> and <paramref name="j"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.union_step")]
    public static void UnionStep<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i, SpecInt j) => throw Ghost();

    /// <summary>A lemma: with <paramref name="t"/> used up (<c>j == t.Length</c>), the rest of the merge is the rest of <paramref name="s"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.union_rest_left")]
    public static void UnionRestLeft<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i, SpecInt j) => throw Ghost();

    /// <summary>A lemma: with <paramref name="s"/> used up (<c>i == s.Length</c>), the rest of the merge is the rest of <paramref name="t"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.union_rest_right")]
    public static void UnionRestRight<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i, SpecInt j) => throw Ghost();

    /// <summary>A lemma: the merge of the whole sequences, as suffixes from 0.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.union_whole")]
    public static void UnionWhole<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: the merge with an empty <paramref name="s"/> is <paramref name="t"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.union_left_empty")]
    public static void UnionLeftEmpty<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: for an empty <paramref name="s"/> and a strictly sorted <paramref name="t"/>,
    /// <see cref="SymmetricExcept"/> is <see cref="Union"/>, both being <paramref name="t"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.sym_except_union_empty")]
    public static void SymmetricExceptUnionEmpty<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: the merge of two strictly sorted sequences is strictly sorted and no longer than both.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.union_sorted")]
    public static void UnionSorted<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: writing <c>x</c> at <paramref name="k"/> of <paramref name="m"/> moves it from the front of <c>x :: r</c> to the prefix.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.push_prefix")]
    public static void PushPrefix<T>(Seq<T> m, SpecInt k, T x, Seq<T> r) => throw Ghost();

    /// <summary>A lemma: writing <c>s[i]</c> at <paramref name="k"/> of <paramref name="m"/> moves it from the suffix of <paramref name="s"/> from <paramref name="i"/> to the prefix.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.push_rest")]
    public static void PushRest<T>(Seq<T> m, SpecInt k, Seq<T> s, SpecInt i) => throw Ghost();

    /// <summary><paramref name="s"/> after adding each element of <paramref name="t"/>, first to last, unless a member compares equal to it (<c>AddAllElements</c>).</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.add_all")]
    public static Seq<T> AddAll<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: adding <c>t[i]</c> extends the prefix <c>t[0..i)</c> by one.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.add_all_step")]
    public static void AddAllStep<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i) => throw Ghost();

    /// <summary>A lemma: the whole of <paramref name="t"/> is its prefix of its length.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.add_all_whole")]
    public static void AddAllWhole<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: adding the first <paramref name="i"/> elements of <paramref name="t"/> adds at most <paramref name="i"/> elements.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.add_all_length")]
    public static void AddAllLength<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i) => throw Ghost();

    /// <summary>A lemma: when one side is used up (<c>i == s.Length</c> or <c>j == t.Length</c>), the rest of the merge is the rest of the other.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.union_rest")]
    public static void UnionRest<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i, SpecInt j) => throw Ghost();

    /// <summary>A lemma: <paramref name="p"/> followed by the empty suffix of <paramref name="s"/> is <paramref name="p"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetUnion.rest_done")]
    public static void RestDone<T>(Seq<T> p, Seq<T> s) => throw Ghost();
}
