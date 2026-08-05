// The §7.2 variant of `test/switch_stmt`: the same rule (R5.14) reached through a different
// program, written without looking at what the translator does. Nothing here shares a
// shape with `Switch.cs`:
//
//   * every section ends in `return`, not `break`, so the chain is a chain of guards and
//     the statement after the `switch` is what its missing `else` stands for;
//   * there is no `default` at all;
//   * the labels are written in descending order, and the stacked pair is written last;
//   * the loop is a `while` with an explicit measure, and the arm that skips does so by
//     doing nothing rather than by `continue`.
//
// A translator change needed to make this file verify would mean R5.14 had been fitted to
// `Switch.cs` rather than derived.
using PalLang;

namespace PalCSharp.Tests;

public static class Dispatching
{
    /// <summary>The weight of one tag.</summary>
    [Spec]
    public static SpecInt Weight(SpecInt t) =>
        t == 9 ? 5 :
        t == 4 ? 3 :
        t == 2 || t == 3 ? 1 : 0;

    /// <summary>
    /// Sections that return. There is no `default`, so control leaves the `switch` for
    /// the statement after it whenever no label matches — which is the one exit the chain
    /// of guards does not take.
    /// </summary>
    [Ensures("Result == Weight(t)")]
    public static int WeightOf(int t)
    {
        switch (t)
        {
            case 9:
                return 5;
            case 4:
                return 3;
            case 3:
            case 2:
                return 1;
        }
        return 0;
    }

    /// <summary>The total weight of the first `n` tags of `s`.</summary>
    [Spec(Recursive = true)]
    [Requires("0 <= n && n <= s.Length")]
    [Decreases("n")]
    public static SpecInt Load(Seq<int> s, SpecInt n) =>
        n == 0 ? 0 : Load(s, n - 1) + Weight(s[n - 1]);

    /// <summary>One unfolding of `Load`.</summary>
    [Lemma]
    [Requires("0 <= n && n + 1 <= s.Length")]
    [Ensures("Load(s, n + 1) == Load(s, n) + Weight(s[n])")]
    [System.Diagnostics.Conditional("PAL")]
    public static void LoadStep(Seq<int> s, int n) { }

    /// <summary>
    /// A `switch` inside a `while`, accumulating rather than counting. Each weight is at
    /// most 5, so the running total is bounded by five times the index — which is what
    /// makes the additions safe, and is stated as an invariant because every partial sum
    /// is actually computed.
    /// </summary>
    [Requires("a.Length <= 1000000")]
    [Ensures("Result == Load(Contents(a), a.Length)")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    public static int TotalLoad(int[] a)
    {
        int sum = 0;
        int k = 0;
        while (k < a.Length)
        {
            Pal.Invariant(0 <= k && k <= a.Length);
            Pal.Invariant(a.Length <= 1000000);
            Pal.Invariant(0 <= sum && sum <= 5 * k);
            Pal.Invariant(sum == Load(Pal.Contents(a), k));
            Pal.Decreases(a.Length - k);
            LoadStep(Pal.Contents(a), k);
            switch (a[k])
            {
                case 9:
                    sum += 5;
                    break;
                case 4:
                    sum += 3;
                    break;
                case 3:
                case 2:
                    sum += 1;
                    break;
            }
            k++;
        }
        return sum;
    }
}
