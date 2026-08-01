using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Variant of <see cref="Arrays"/> (plan §7.2). Same contract, same algorithm,
/// different C#: a counted `for` loop over the first half instead of a `while` with
/// two moving ends, so the second index is an expression rather than a local, the
/// swap is written through a differently-named temporary, and the measure is
/// inferred from the loop rather than given. It must verify unchanged.
/// </summary>
public static class ArraysVariant
{
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < Contents(a).Length, " +
             "Contents(a)[k] == Old(Contents(a))[Contents(a).Length - 1 - k]))")]
    public static void Reverse(int[] a)
    {
        int n = a.Length;
        for (int i = 0; i < n - 1 - i; i++)
        {
            Pal.Invariant(n == Pal.Contents(a).Length);
            Pal.Invariant(Pal.Contents(a).Length == Pal.Old(Pal.Contents(a)).Length);
            Pal.Invariant(0 <= i && 2 * i <= Pal.Contents(a).Length);
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(
                (0 <= k && k < i) || (Pal.Contents(a).Length - 1 - i < k && k < Pal.Contents(a).Length),
                Pal.Contents(a)[k] == Pal.Old(Pal.Contents(a))[Pal.Contents(a).Length - 1 - k])));
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(
                i <= k && k <= Pal.Contents(a).Length - 1 - i,
                Pal.Contents(a)[k] == Pal.Old(Pal.Contents(a))[k])));

            int mirror = n - 1 - i;
            int saved = a[i];
            a[i] = a[mirror];
            a[mirror] = saved;
        }
    }
}
