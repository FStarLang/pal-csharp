using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R27.49. Comparing two sequences position by position under a comparer, as
/// <c>SortedSet&lt;T&gt;.SetEquals</c> does when it walks two sets of one comparer in step.
/// <c>Pulse.Lib.CSharp.SetCompare</c>; a <c>void</c> member is a lemma, called as a ghost
/// statement. On strictly sorted sequences <c>SameKeys</c> is equality of the sets they hold
/// (<c>same_keys_members</c> in the library).
/// </summary>
public static class SpecSetCompare
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecSetCompare is a specification-only construct and has no runtime meaning.");

    /// <summary>
    /// <paramref name="s"/> and <paramref name="t"/> have the same length and compare equal
    /// under <paramref name="c"/> position by position.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SetCompare.same_keys")]
    public static bool SameKeys<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();

    /// <summary>A lemma: one step of a walk over the suffixes <c>s[i..]</c> and <c>t[j..]</c>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetCompare.same_keys_step")]
    public static void SameKeysStep<T>(IComparer<T> c, Seq<T> s, Seq<T> t, SpecInt i, SpecInt j) => throw Ghost();

    /// <summary>A lemma: the whole sequences are their suffixes from 0.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetCompare.same_keys_whole")]
    public static void SameKeysWhole<T>(IComparer<T> c, Seq<T> s, Seq<T> t) => throw Ghost();
}
