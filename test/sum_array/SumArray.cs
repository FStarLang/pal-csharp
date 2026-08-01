using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Reading an array in a counted loop, with a postcondition that says what the loop
/// computes rather than merely that it terminates. The connection to the recursive
/// specification is what makes this a correctness proof: `Result >= 0` would prove
/// nothing.
/// </summary>
public static class Summing
{
    /// <summary>The sum of the first `n` elements of `s`.</summary>
    [Spec(Recursive = true)]
    [Requires("0 <= n && n <= s.Length")]
    [Decreases("n")]
    public static SpecInt SumUpTo(Seq<int> s, SpecInt n) =>
        n == 0 ? 0 : SumUpTo(s, n - 1) + s[n - 1];

    /// <summary>
    /// Every partial sum is representable as an `int`. This is the no-overflow
    /// obligation, and it is about *every* prefix, not just the whole: every prefix
    /// sum is actually computed, so every one of them must fit.
    /// </summary>
    [Spec]
    public static bool SumsFit(Seq<int> s) =>
        Pal.Forall((int k) => Pal.Implies(
            0 <= k && k <= s.Length,
            int.MinValue <= SumUpTo(s, k) && SumUpTo(s, k) <= int.MaxValue));

    /// <summary>
    /// One unfolding of `SumUpTo`, as a fact the prover can be pointed at. F* will
    /// not unfold a recursive definition inside a loop invariant on its own.
    /// </summary>
    [Lemma]
    [Requires("0 <= n && n + 1 <= s.Length")]
    [Ensures("SumUpTo(s, n + 1) == SumUpTo(s, n) + s[n]")]
    [System.Diagnostics.Conditional("PAL")]
    public static void SumUpToStep(Seq<int> s, int n) { }

    [Requires("SumsFit(Contents(a))")]
    [Ensures("Result == SumUpTo(Contents(a), a.Length)")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    public static int Sum(int[] a)
    {
        int total = 0;
        for (int i = 0; i < a.Length; i++)
        {
            // A Pulse loop body sees the invariant and nothing else, so a
            // precondition the body still needs has to be restated here.
            Pal.Invariant(SumsFit(Pal.Contents(a)));
            Pal.Invariant(0 <= i && i <= Pal.Contents(a).Length);
            Pal.Invariant(total == SumUpTo(Pal.Contents(a), i));
            SumUpToStep(Pal.Contents(a), i);
            total += a[i];
        }
        return total;
    }
}
