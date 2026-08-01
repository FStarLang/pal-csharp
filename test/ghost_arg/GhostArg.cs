using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Ghost parameters. <c>Ghost&lt;T&gt;</c> is an empty <c>readonly struct</c> declared
/// as an optional parameter, so a ghost argument costs nothing, callers need never
/// mention it, and the C# compiler still type-checks every specification that does.
/// It erases to an implicit <c>(#s: erased t)</c> binder in Pulse.
/// </summary>
/// <remarks>
/// Known limitation, inherited from Pulse and shared with PAL: a ghost argument is
/// resolved by unification at the call site, so one that appears only in the *pure*
/// part of a contract — like <c>s</c> below — cannot be inferred, and such a method
/// cannot yet be called from translated C#. Ghost arguments that appear in a
/// separation-logic conjunct are inferred from the resource and call fine.
/// </remarks>
public static class GhostArgs
{
    [Requires("Contents(a) == s")]
    [Requires("0 <= i && i < s.Length")]
    [Ensures("Contents(a) == s")]
    [Ensures("Result == s[i]")]
    public static int Lookup(int[] a, int i, Ghost<Seq<int>> s = default)
    {
        return a[i];
    }

    /// <summary>Two ghost arguments, one of them a specification-only integer.</summary>
    [Requires("Contents(a) == s")]
    [Requires("n == s.Length")]
    [Ensures("Result == n")]
    public static int Size(int[] a, Ghost<Seq<int>> s = default, Ghost<SpecInt> n = default)
    {
        return a.Length;
    }
}
