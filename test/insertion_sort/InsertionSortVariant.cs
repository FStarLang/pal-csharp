using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Variant of <see cref="Sorting"/> (plan §7.2). The same algorithm with the same
/// contract, written with an explicit `while` instead of a `for`, with the loop
/// counter incremented at the top rather than the bottom, with every local renamed,
/// and with the guard's operands exchanged (`key &lt; a[k]` rather than
/// `a[k] &gt; key`). None of that is visible to the translation scheme, so it must
/// verify with no change to the translator.
/// </summary>
public static class SortingVariant
{
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("IsPermutation(Contents(a), Old(Contents(a)))")]
    public static void InsertionSort(int[] a)
    {
        int next = 1;
        while (next < a.Length)
        {
            Pal.Invariant(1 <= next);
            Pal.Invariant(Pal.Contents(a).Length == Pal.Old(Pal.Contents(a)).Length);
            Pal.Invariant(Pal.IsPermutation(Pal.Contents(a), Pal.Old(Pal.Contents(a))));
            Pal.Decreases(int.MaxValue - next);

            int held = a[next];
            int k = next - 1;
            while (k >= 0 && held < a[k])
            {
                Pal.Invariant(-1 <= k && k < next);
                Pal.Invariant(next < Pal.Contents(a).Length);
                Pal.Invariant(Pal.Contents(a).Length == Pal.Old(Pal.Contents(a)).Length);
                Pal.Invariant(Pal.IsPermutation(
                    Pal.SetAt(Pal.Contents(a), k + 1, held),
                    Pal.Old(Pal.Contents(a))));
                Pal.Decreases(k + 1);

                PalSeq.UpdShiftIsPermutation(a, k, held);

                a[k + 1] = a[k];
                k--;
            }
            a[k + 1] = held;
            next++;
        }
    }
}
