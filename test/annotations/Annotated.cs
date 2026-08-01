using System.Diagnostics;
using PalLang;

namespace PalCSharp.Test;

/// <summary>
/// Exercises the whole annotation surface, so that the erasure checker in
/// <see cref="Program"/> can confirm that none of it survives into the IL of a
/// build in which <c>PAL</c> is not defined.
/// </summary>
public static class Annotated
{
    // -- Pure specification functions --------------------------------------

    [Spec]
    public static bool Sorted(int[] a, int lo, int hi) =>
        Pal.Forall((int i, int j) =>
            Pal.Implies(lo <= i && i < j && j < hi, a[i] <= a[j]));

    [Spec]
    public static SpecInt SumUpTo(SpecInt n) => n * (n + 1) / 2;

    // -- Lemmas ------------------------------------------------------------

    [Lemma]
    [Requires("0 <= i && i < a.Length")]
    [Requires("0 <= j && j < a.Length")]
    [Ensures("IsPermutation(Contents(a), Old(Contents(a)))")]
    [Conditional("PAL")]
    public static void PermSwap(int[] a, int i, int j) { }

    // -- Scalars, ref and out ----------------------------------------------

    [Ensures("x == Old(y) && y == Old(x)")]
    public static void Swap(ref int x, ref int y)
    {
        int t = x;
        x = y;
        y = t;
    }

    [Ensures("Result >= x && Result >= y")]
    [Ensures("Result == x || Result == y")]
    public static int Max(int x, int y) => x > y ? x : y;

    [Requires("d != 0")]
    [Ensures("q * d + r == n")]
    public static void DivMod(int n, int d, out int q, out int r)
    {
        q = n / d;
        r = n - q * d;
    }

    // -- Arrays, loops and invariants --------------------------------------

    [Requires("a != null")]
    [Ensures("Result >= 0")]
    public static int CountPositive(int[] a)
    {
        int count = 0;
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(0 <= count && count <= i);
            Pal.Decreases(a.Length - i);
            if (a[i] > 0) count++;
        }
        Pal.Assert(count >= 0);
        return count;
    }

    /// <summary>The M1 headline: a stateful, short-circuiting loop guard.</summary>
    [Ensures("Sorted(a, 0, a.Length)")]
    [Ensures("IsPermutation(Contents(a), Old(Contents(a)))")]
    public static void InsertionSort(int[] a)
    {
        for (int i = 1; i < a.Length; i++)
        {
            Pal.Invariant(1 <= i && i <= a.Length);
            Pal.Invariant(Sorted(a, 0, i));
            Pal.Invariant(
                Pal.IsPermutation(Pal.Contents(a),
                                          Pal.Old(Pal.Contents(a))));
            Pal.Decreases(a.Length - i);

            int key = a[i];
            int j = i - 1;
            while (j >= 0 && a[j] > key)
            {
                Pal.Invariant(-1 <= j && j < i);
                Pal.Decreases(j + 1);
                a[j + 1] = a[j];
                j--;
            }
            PermSwap(a, j + 1, i);
            a[j + 1] = key;
        }
    }

    // -- Ghost parameters and raw Pulse escape hatches ----------------------

    [Requires("0 <= n")]
    [Ensures("Result == n")]
    public static int Identity(int n, Ghost<Seq<int>> witness = default)
    {
        Pal.GhostStmt("Pulse.Lib.CSharp.Seq.reveal_id $(witness)");
        Pal.Assume(Pal.InlinePulse("True"));
        return n;
    }
}
