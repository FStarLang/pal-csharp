using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Binary search, with both halves of correctness proved: when it reports success the
/// index it returns really holds the key, and when it reports failure the key really
/// is absent. The second half is the one that needs the sortedness precondition.
/// </summary>
public static class Searching
{
    [Spec]
    [Requires("0 <= lo && lo <= hi && hi <= s.Length")]
    public static bool Sorted(Seq<int> s, SpecInt lo, SpecInt hi) =>
        Pal.Forall((int i, int j) => Pal.Implies(lo <= i && i < j && j < hi, s[i] <= s[j]));

    [Requires("Sorted(Contents(a), 0, Contents(a).Length)")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    [Ensures("Implies(Result, 0 <= index && index < Contents(a).Length && Contents(a)[index] == key)")]
    [Ensures("Implies(!Result, Forall((int k) => Implies(" +
             "0 <= k && k < Contents(a).Length, Contents(a)[k] != key)))")]
    public static bool Search(int[] a, int key, out int index)
    {
        index = 0;
        bool found = false;
        int lo = 0;
        int hi = a.Length;

        while (lo < hi && !found)
        {
            Pal.Invariant(0 <= lo && lo <= hi && hi <= Pal.Contents(a).Length);
            Pal.Invariant(Pal.Contents(a) == Pal.Old(Pal.Contents(a)));
            Pal.Invariant(Sorted(Pal.Contents(a), 0, Pal.Contents(a).Length));
            Pal.Invariant(Pal.Implies(found,
                0 <= index && index < Pal.Contents(a).Length && Pal.Contents(a)[index] == key));
            // Everything already excluded from the search window is not the key.
            Pal.Invariant(Pal.Implies(!found, Pal.Forall((int k) => Pal.Implies(
                (0 <= k && k < lo) || (hi <= k && k < Pal.Contents(a).Length),
                Pal.Contents(a)[k] != key))));
            // The window does not shrink on the iteration that finds the key --
            // that iteration terminates the loop by setting `found` instead.
            Pal.Decreases(hi - lo);

            int mid = lo + (hi - lo) / 2;
            // `mid` lies inside the window. Every index and increment below
            // depends on this, and the solver needs the division step spelled
            // out before it will believe it.
            Pal.Assert(lo < hi);
            Pal.Assert(0 <= (hi - lo) / 2);
            Pal.Assert(lo <= mid && mid < hi);
            int probe = a[mid];
            if (probe == key)
            {
                index = mid;
                found = true;
                // Narrowing the window on the hit as well keeps `hi - lo` a
                // decreasing measure on every path through the loop.
                lo = mid + 1;
            }
            else if (probe < key)
            {
                // Sortedness turns one comparison into a fact about the whole
                // lower half: nothing at or below `mid` can be the key.
                Pal.Assert(Pal.Forall((int k) => Pal.Implies(
                    0 <= k && k <= mid, Pal.Contents(a)[k] != key)));
                lo = mid + 1;
            }
            else
            {
                Pal.Assert(Pal.Forall((int k) => Pal.Implies(
                    mid <= k && k < Pal.Contents(a).Length, Pal.Contents(a)[k] != key)));
                hi = mid;
            }
        }

        return found;
    }
}
