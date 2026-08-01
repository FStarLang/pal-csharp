// The §7.2 contortion detector for R4.9: the same two contracts, written differently —
// `while` for `for`, a descending scan for an ascending one, the permission variables
// renamed and given in the other order, the agreement predicate stated over a suffix
// rather than a prefix.
using PalLang;

public static class CompareVariant
{
    /// <summary>The two sequences agree on every index in <c>[n, s.Length)</c>.</summary>
    [Spec]
    public static bool AgreeAbove(Seq<int> s, Seq<int> t, SpecInt n) =>
        Pal.Forall((SpecInt k) =>
            Pal.Implies(n <= k && 0 <= k && k < s.Length && k < t.Length, s[k] == t[k]));

    [Requires("x.Length == y.Length")]
    [Ensures("Implies(Result, CompareVariant.AgreeAbove(Contents(x), Contents(y), 0))")]
    [Ensures("Implies(!Result, Exists((SpecInt k) => " +
             "0 <= k && k < x.Length && Contents(x)[k] != Contents(y)[k]))")]
    public static bool Same([Frac("q")] int[] x, [Frac("r")] int[] y)
    {
        bool differs = false;
        int j = x.Length;
        while (j > 0 && !differs)
        {
            Pal.Invariant(0 <= j && j <= x.Length);
            Pal.Invariant(Pal.Implies(!differs, AgreeAbove(Pal.Contents(x), Pal.Contents(y), j)));
            Pal.Invariant(Pal.Implies(differs, Pal.Exists((SpecInt k) =>
                0 <= k && k < x.Length && Pal.Contents(x)[k] != Pal.Contents(y)[k])));
            Pal.Decreases(j);
            // `j` is decremented on every path, including the one that gives up. A
            // measure that stalls on the iteration which stops the loop is the commonest
            // reason a correct loop fails to verify, and the fix belongs here, in the C#,
            // not in the translator.
            if (x[j - 1] != y[j - 1])
            {
                differs = true;
            }
            j = j - 1;
        }
        return !differs;
    }

    [Requires("x.Length == y.Length")]
    [Ensures("0 <= Result && Result <= x.Length")]
    [Ensures("Implies(CompareVariant.AgreeAbove(Contents(x), Contents(y), 0), Result == x.Length)")]
    public static int Matches([Frac("q")] int[] x, [Frac("r")] int[] y)
    {
        int hits = 0;
        int j = x.Length;
        while (j > 0)
        {
            Pal.Invariant(0 <= j && j <= x.Length);
            Pal.Invariant(0 <= hits && hits <= x.Length - j);
            Pal.Invariant(Pal.Implies(
                AgreeAbove(Pal.Contents(x), Pal.Contents(y), j), hits == x.Length - j));
            Pal.Decreases(j);
            if (x[j - 1] == y[j - 1])
            {
                hits = hits + 1;
            }
            j = j - 1;
        }
        return hits;
    }
}
