// The §7.2 contortion detector for R5.11: the same two contracts, written differently.
// `Find` becomes a `while` with a user-supplied measure and an inverted test; the escape
// is nested one block deeper. `CountNonZero` becomes a `while` whose increment happens
// *before* the `continue` — the C#-equivalent restructuring, which is the one that
// distinguishes a correct `for`-step rule from an accidental one.
//
// Both must verify with no change to the translator.
using PalLang;

public static class EscapesVariant
{
    [Spec]
    public static bool NoneZero(Seq<int> s, SpecInt lo, SpecInt hi) =>
        Pal.Forall((SpecInt k) =>
            Pal.Implies(lo <= k && k < hi && 0 <= k && k < s.Length, s[k] != 0));

    [Ensures("Result == -1 || (0 <= Result && Result < a.Length && Contents(a)[Result] == key)")]
    public static int Locate(int[] a, int key)
    {
        int hit = -1;
        int p = 0;
        while (p < a.Length)
        {
            Pal.Invariant(0 <= p && p <= a.Length);
            Pal.Invariant(hit == -1 ||
                (0 <= hit && hit < a.Length && Pal.Contents(a)[hit] == key));
            Pal.Decreases(a.Length - p);
            if (a[p] != key)
            {
                p = p + 1;
            }
            else
            {
                hit = p;
                break;
            }
        }
        return hit;
    }

    [Ensures("0 <= Result && Result <= a.Length")]
    [Ensures("Implies(EscapesVariant.NoneZero(Contents(a), 0, a.Length), Result == a.Length)")]
    public static int Tally(int[] a)
    {
        int seen = 0;
        int total = 0;
        while (seen < a.Length)
        {
            Pal.Invariant(0 <= seen && seen <= a.Length);
            Pal.Invariant(0 <= total && total <= seen);
            Pal.Invariant(Pal.Implies(NoneZero(Pal.Contents(a), 0, seen), total == seen));
            Pal.Decreases(a.Length - seen);
            int here = a[seen];
            seen = seen + 1;
            if (here == 0)
            {
                continue;
            }
            total = total + 1;
        }
        return total;
    }
}
