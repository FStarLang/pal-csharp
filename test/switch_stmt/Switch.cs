// R5.14. `switch` is a notation for an if/else chain, and this file is written so that
// the three places the notation is *not* a transparent one would fail.
//
//   * `default` is written in the middle of the sections, where C# allows it and where a
//     chain that kept the written order would give it the wrong meaning.
//   * A section runs `continue` inside a `for`, which must still reach the loop — and
//     must still run the loop's step, or the measure stalls (R5.10).
//   * The scrutinee is `a[i++]`, so evaluating it once per arm instead of once would
//     advance the index by three and the postcondition would not hold.
//
// The specification is a total function on the key, and every postcondition is stated
// against it, so what is proved is that the `switch` computes it — not merely that the
// result is in range.
using PalLang;

namespace PalCSharp.Tests;

public static class Switching
{
    /// <summary>What the `switch` on a key is supposed to compute.</summary>
    [Spec]
    public static SpecInt Score(SpecInt k) =>
        k == 0 || k == 1 ? 10 :
        k == 2 ? 20 :
        k == 7 ? 0 : 1;

    /// <summary>
    /// Stacked labels, a `default` written before two of the cases it is the alternative
    /// to, and one arm per result. Reordering `default` to the end is sound only because
    /// C# requires the case labels to be distinct constants; the postcondition is what
    /// checks that the reordering was done right.
    /// </summary>
    [Ensures("Result == Score(k)")]
    public static int ScoreOf(int k)
    {
        int r = 0;
        switch (k)
        {
            case 0:
            case 1:
                r = 10;
                break;
            default:
                r = 1;
                break;
            case 2:
                r = 20;
                break;
            case 7:
                r = 0;
                break;
        }
        return r;
    }

    /// <summary>How many of the first `n` entries of `s` score 10.</summary>
    [Spec(Recursive = true)]
    [Requires("0 <= n && n <= s.Length")]
    [Decreases("n")]
    public static SpecInt Hits(Seq<int> s, SpecInt n) =>
        n == 0 ? 0 : Hits(s, n - 1) + (Score(s[n - 1]) == 10 ? 1 : 0);

    /// <summary>One unfolding of `Hits`, which F* will not perform under an invariant.</summary>
    [Lemma]
    [Requires("0 <= n && n + 1 <= s.Length")]
    [Ensures("Hits(s, n + 1) == Hits(s, n) + (Score(s[n]) == 10 ? 1 : 0)")]
    [System.Diagnostics.Conditional("PAL")]
    public static void HitsStep(Seq<int> s, int n) { }

    /// <summary>
    /// A `switch` inside a loop. The `continue` in the `case 7` arm is the point: inside
    /// a `switch`, `break` leaves the switch and `continue` leaves the iteration, and
    /// only the second of those survives the rewrite unchanged.
    /// </summary>
    [Ensures("Result == Hits(Contents(a), a.Length)")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    public static int Count(int[] a)
    {
        int count = 0;
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(0 <= count && count <= i);
            Pal.Invariant(count == Hits(Pal.Contents(a), i));
            HitsStep(Pal.Contents(a), i);
            switch (a[i])
            {
                case 0:
                case 1:
                    count++;
                    break;
                case 7:
                    continue;
                default:
                    break;
            }
        }
        return count;
    }

    /// <summary>
    /// The same count, with the index advanced by the scrutinee itself. C# evaluates the
    /// governing expression once, so `i` advances once per iteration; a chain that
    /// re-evaluated `a[i++]` per arm would advance it up to three times and the loop
    /// would run off the end.
    /// </summary>
    [Ensures("Result == Hits(Contents(a), a.Length)")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    public static int CountStepping(int[] a)
    {
        int count = 0;
        int i = 0;
        while (i < a.Length)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(0 <= count && count <= i);
            Pal.Invariant(count == Hits(Pal.Contents(a), i));
            Pal.Decreases(a.Length - i);
            HitsStep(Pal.Contents(a), i);
            switch (a[i++])
            {
                case 0:
                case 1:
                    count++;
                    break;
                default:
                    break;
            }
        }
        return count;
    }
}
