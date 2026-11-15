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

    [Requires("a.Length > 0")]
    public static void Touch(int[] a)
    {
        a[0] = 0;
    }

    [Requires("a.Length > 0")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    public static void CallRepeatedly(int[] a)
    {
        for (int i = 0; i < 2; i++)
        {
            Pal.Invariant(0 <= i && i <= 2);
            Touch(a);
        }
    }

    [Requires("a.Length > 0")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    public static void CallNested(int[] a)
    {
        for (int i = 0; i < 2; i++)
        {
            Pal.Invariant(0 <= i && i <= 2);
            for (int j = 0; j < 2; j++)
            {
                Pal.Invariant(0 <= j && j <= 2);
                Touch(a);
            }
        }
        CallRepeatedly(a);
    }

    [Requires("a.Length > 0")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    public static void CallWithExits(int[] a)
    {
        for (int i = 0; i < 3; i++)
        {
            Pal.Invariant(0 <= i && i <= 3);
            if (i == 0) continue;
            Touch(a);
            if (i == 1) break;
        }
    }

    [Requires("a.Length > 0")]
    [Ensures("!Result")]
    public static bool TouchCondition(int[] a)
    {
        a[0] = 0;
        return false;
    }

    [Requires("a.Length > 0")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    public static void CallInGuard(int[] a)
    {
        while (TouchCondition(a))
        {
            Pal.Decreases(0);
        }
    }

    [Requires("n >= 0")]
    [Ensures("Result == n")]
    public static int AllocateAndFill(int n)
    {
        int[] a = new int[n];
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i && i <= n);
            Pal.Decreases(n - i);
            a[i] = 0;
            i++;
        }
        return a.Length;
    }
}
