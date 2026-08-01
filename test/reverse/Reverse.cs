using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// In-place array writes with a quantified postcondition. The postcondition is the
/// definition of "reversed" — every cell related to the cell it came from — rather
/// than a structural property that any permutation would satisfy.
/// </summary>
public static class Arrays
{
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < Contents(a).Length, " +
             "Contents(a)[k] == Old(Contents(a))[Contents(a).Length - 1 - k]))")]
    public static void Reverse(int[] a)
    {
        int lo = 0;
        int hi = a.Length - 1;
        while (lo < hi)
        {
            Pal.Invariant(0 <= lo && hi < Pal.Contents(a).Length);
            // Keeps the measure below non-negative, which a `decreases` needs.
            Pal.Invariant(lo <= hi + 1);
            Pal.Invariant(lo + hi == Pal.Contents(a).Length - 1);
            Pal.Invariant(Pal.Contents(a).Length == Pal.Old(Pal.Contents(a)).Length);
            // Outside the window, every cell already holds its mirror image.
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(
                (0 <= k && k < lo) || (hi < k && k < Pal.Contents(a).Length),
                Pal.Contents(a)[k] == Pal.Old(Pal.Contents(a))[Pal.Contents(a).Length - 1 - k])));
            // Inside it, nothing has been touched.
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(
                lo <= k && k <= hi,
                Pal.Contents(a)[k] == Pal.Old(Pal.Contents(a))[k])));
            Pal.Decreases(hi - lo + 1);

            int t = a[lo];
            a[lo] = a[hi];
            a[hi] = t;
            lo++;
            hi--;
        }
    }
}
