// EXPECT-PULSE: spec_MissingLemma_SumUpTo
// R4.7. A recursive `[Spec]` function is not unfolded at a symbolic index, so the step
// relating the accumulator before an iteration to the accumulator after it has to be
// supplied as a lemma call. This is the summation from `test/sum_array` with exactly that
// call -- `SumUpToStep` -- deleted, and nothing else changed.
//
// So this is the case for the ergonomic claim as much as the soundness one. The proof step
// a user writes is an ordinary C# method call that type-checks, renames under refactoring,
// and compiles to nothing; leaving it out has to fail rather than quietly prove something
// weaker, which is the only property that makes writing it worthwhile.
//
// The expectation names the recursive specification rather than a failed property, because
// there is no failed property to name: the query is large enough that F* prints
// `Try with --query_stats` in place of the VC and leaves only the context, in which
// `spec_MissingLemma_SumUpTo` is the definition the proof is stuck on. That is a real
// limit on what a user is told here, and it is recorded rather than papered over.
using PalLang;

public static class MissingLemma
{
    [Spec(Recursive = true)]
    [Requires("0 <= n && n <= s.Length")]
    [Decreases("n")]
    public static SpecInt SumUpTo(Seq<int> s, SpecInt n) =>
        n == 0 ? 0 : SumUpTo(s, n - 1) + s[n - 1];

    [Spec]
    public static bool SumsFit(Seq<int> s) =>
        Pal.Forall((int k) => Pal.Implies(
            0 <= k && k <= s.Length,
            int.MinValue <= SumUpTo(s, k) && SumUpTo(s, k) <= int.MaxValue));

    [Requires("SumsFit(Contents(a))")]
    [Ensures("Result == SumUpTo(Contents(a), a.Length)")]
    public static int Sum(int[] a)
    {
        int total = 0;
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(SumsFit(Pal.Contents(a)));
            Pal.Invariant(0 <= i && i <= Pal.Contents(a).Length);
            Pal.Invariant(total == SumUpTo(Pal.Contents(a), i));
            // MARKER
            total += a[i];
        }
        return total;
    }
}
