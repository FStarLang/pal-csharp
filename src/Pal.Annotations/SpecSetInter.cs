using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R27.50. The intersection of two sorted sequences under a comparer, as
/// <c>SortedSet&lt;T&gt;.IntersectWith</c> merges two sets of one comparer.
/// <c>Pulse.Lib.CSharp.SetInter</c>; a <c>void</c> member is a lemma, called as a ghost
/// statement.
/// </summary>
public static class SpecSetInter
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecSetInter is a specification-only construct and has no runtime meaning.");

    /// <summary>
    /// The elements of <paramref name="t"/> that compare equal under <paramref name="c"/> to
    /// some element of <paramref name="s"/>, in <paramref name="t"/>'s order.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SetInter.inter")]
    public static Seq<T> Inter<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: one merge step over the strictly sorted suffixes <c>s[i..]</c> and <c>t[j..]</c>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetInter.inter_step")]
    public static void InterStep<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i, SpecInt j) => throw Ghost();

    /// <summary>
    /// A lemma: the suffix intersection is empty when <c>s</c> or <c>t</c> is used up, or
    /// <c>t[j]</c> is above the last of <c>s</c>.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SetInter.inter_done")]
    public static void InterDone<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i, SpecInt j) => throw Ghost();

    /// <summary>A lemma: the whole sequences are their suffixes from 0.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetInter.inter_whole")]
    public static void InterWhole<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: the intersection with a strictly sorted <c>t</c> is strictly sorted and no longer than <c>t</c>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetInter.inter_sorted")]
    public static void InterSorted<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: nothing intersects an empty <c>s</c>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetInter.inter_left_empty")]
    public static void InterLeftEmpty<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>
    /// A lemma: when the merge has stopped (as for <see cref="InterDone{T}"/>), a prefix
    /// <c>p</c> followed by the suffix intersection is the intersection, so <c>p</c> is.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SetInter.inter_finish")]
    public static void InterFinish<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i, SpecInt j, Seq<T> p) => throw Ghost();

    /// <summary>
    /// A lemma: writing <paramref name="x"/> at <paramref name="k"/> of <paramref name="m"/>
    /// extends the prefix <c>m[0..k)</c> by <paramref name="x"/>, ahead of any rest <paramref name="r"/>.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SetInter.push_prefix")]
    public static void PushPrefix<T>(Seq<T> m, SpecInt k, T x, Seq<T> r) => throw Ghost();
}
