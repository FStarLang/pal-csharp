using System;
using System.Collections.Generic;

namespace PalLang;

/// <summary>
/// R27.40. Membership in a sequence, and the ghost steps of a set's filtering removal
/// (<c>SortedSet&lt;T&gt;.RemoveWhere</c>): removing, one at a time, the members of a list of
/// matches from a strictly sorted sequence. <c>Pulse.Lib.CSharp.SetFilter</c>; a <c>void</c>
/// member is a lemma, called as a ghost statement.
/// </summary>
public static class SpecSetFilter
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecSetFilter is a specification-only construct and has no runtime meaning.");

    /// <summary>Some element of <paramref name="s"/> is <paramref name="y"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetFilter.contains")]
    public static bool Contains<T>(Seq<T> s, T y) => throw Ghost();

    /// <summary>
    /// <paramref name="m"/>'s elements past <paramref name="i"/> have been removed from the
    /// strictly sorted <paramref name="s0"/>, leaving the strictly sorted <paramref name="s"/>;
    /// every one of <paramref name="m"/> is a member of <paramref name="s0"/>.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.SetFilter.removing")]
    public static bool Removing<T>(IComparer<T> c, Seq<T> s0, Seq<T> s, Seq<T> m, SpecInt i) => throw Ghost();

    /// <summary>A lemma: nothing removed yet.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetFilter.removing_start")]
    public static void RemovingStart<T>(IComparer<T> c, Seq<T> s0, Seq<T> m) => throw Ghost();

    /// <summary>A lemma: removing <c>m[i]</c> from <paramref name="s"/> (if present) continues the removal.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetFilter.removing_step")]
    public static void RemovingStep<T>(IComparer<T> c, Seq<T> s0, Seq<T> s, Seq<T> m, SpecInt i) => throw Ghost();

    /// <summary>A lemma: the strictly sorted set of <paramref name="s0"/>'s members <paramref name="match"/> rejects is <c>Pal.RemoveAll(s0, match)</c>.</summary>
    [SpecOp("Pulse.Lib.CSharp.SetFilter.filter_unique")]
    public static void FilterUnique<T>(IComparer<T> c, Seq<T> s0, Seq<T> s, Predicate<T> match) => throw Ghost();
}
