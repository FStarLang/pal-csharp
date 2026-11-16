using System.Diagnostics;
using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R30.36. <c>Pal.Join</c> after an <c>if</c>: the arms meet again, holding the frame and
/// the stated facts, and what follows is emitted once rather than once per arm. A loop in
/// an arm that a <c>return</c> may leave completes that <c>return</c> after the join.
/// </summary>
public static class JoinIf
{
    [Ensures("Result >= -2")]
    [Ensures("Pal.Implies(Result >= 0, Result < a.Length && a[Result] == key)")]
    public static int Find(int[] a, int key, bool forward)
    {
        int r = 0;
        if (forward)
        {
            int i = 0;
            while (i < a.Length)
            {
                Pal.Invariant(0 <= i && i <= a.Length);
                Pal.Invariant(Pal.Implies(Pal.Returned(), 0 <= Pal.Result<int>() && Pal.Result<int>() < a.Length && a[Pal.Result<int>()] == key));
                Pal.Decreases(a.Length - i);
                if (a[i] == key) return i;
                i++;
            }
            r = 1;
        }
        else
        {
            int j = a.Length - 1;
            while (j >= 0)
            {
                Pal.Invariant(-1 <= j && j < a.Length);
                Pal.Invariant(Pal.Implies(Pal.Returned(), 0 <= Pal.Result<int>() && Pal.Result<int>() < a.Length && a[Pal.Result<int>()] == key));
                Pal.Decreases(j + 1);
                if (a[j] == key) return j;
                j--;
            }
            r = 2;
        }
        Pal.Join(Pal.Implies(Pal.Returned(), 0 <= Pal.Result<int>() && Pal.Result<int>() < a.Length && a[Pal.Result<int>()] == key));
        Pal.Join(Pal.Implies(!Pal.Returned(), 1 <= r && r <= 2));
        return -r;
    }

    [Ensures("Result >= -2")]
    [Ensures("Pal.Implies(Result >= 0, Result < a.Length && a[Result] == key)")]
    public static int FindSplit(int[] a, int key, bool forward)
    {
        int r = 0;
        if (forward)
        {
            int i = 0;
            while (i < a.Length)
            {
                Pal.Invariant(0 <= i && i <= a.Length);
                Pal.Invariant(Pal.Implies(Pal.Returned(), 0 <= Pal.Result<int>() && Pal.Result<int>() < a.Length && a[Pal.Result<int>()] == key));
                Pal.Decreases(a.Length - i);
                if (a[i] == key) return i;
                i++;
            }
            r = 1;
        }
        else
        {
            int j = a.Length - 1;
            while (j >= 0)
            {
                Pal.Invariant(-1 <= j && j < a.Length);
                Pal.Invariant(Pal.Implies(Pal.Returned(), 0 <= Pal.Result<int>() && Pal.Result<int>() < a.Length && a[Pal.Result<int>()] == key));
                Pal.Decreases(j + 1);
                if (a[j] == key) return j;
                j--;
            }
            r = 2;
        }
        Pal.Join(Pal.Implies(Pal.Returned(), 0 <= Pal.Result<int>() && Pal.Result<int>() < a.Length && a[Pal.Result<int>()] == key));
        Pal.Join(Pal.Implies(!Pal.Returned(), 1 <= r && r <= 2));
        Pal.Split();
        int m = -r;
        return m;
    }
}

[Invariant("0 <= count && count <= items.Length && items.Length == 4")]
public sealed class Slots
{
    private int[] items;
    private int count;

    [Model]
    private SpecInt Model => count;

    [Spec]
    public SpecInt Count => Model;

    [Ensures("@this.Count == 0")]
    public Slots()
    {
        items = new int[4];
        count = 0;
    }

    [Ensures("Pal.Implies(reset, @this.Count == 1)")]
    [Ensures("Pal.Implies(!reset && Old(@this.Count) < 4, @this.Count == Old(@this.Count) + 1)")]
    public void Put(int v, bool reset)
    {
        int before = count;
        int w = v;
        if (reset)
        {
            count = 0;
        }
        else if (count == items.Length)
        {
            count = items.Length - 1;
        }
        Pal.Join(0 <= count && count < items.Length && items.Length == 4);
        Pal.Join(Pal.Implies(reset, count == 0));
        Pal.Join(Pal.Implies(!reset && before < items.Length, count == before));
        items[count] = w;
        count = count + 1;
    }

    [Ensures("Pal.Implies(reset, @this.Count == 1)")]
    [Ensures("Pal.Implies(!reset && Old(@this.Count) < 4, @this.Count == Old(@this.Count) + 1)")]
    public void PutSplit(int v, bool reset)
    {
        int before = count;
        int w = v;
        if (reset)
        {
            count = 0;
        }
        else if (count == items.Length)
        {
            count = items.Length - 1;
        }
        Pal.Join(0 <= count && count < items.Length && items.Length == 4);
        Pal.Join(Pal.Implies(reset, count == 0));
        Pal.Join(Pal.Implies(!reset && before < items.Length, count == before));
        Pal.Join(Pal.Old(this.Count) == before);
        Pal.Split();
        items[count] = w;
        count = count + 1;
    }
}

/// <summary>
/// R30.40. `Big` is opaque while `Halve` is checked: `Result > 0` follows from `Big(x)`
/// only through `BigPos`, the solver never seeing `Big`'s body.
/// </summary>
public static class Opaque
{
    [Spec]
    public static bool Big(int x) => x > 100;

    [Lemma]
    [Requires("Big(x)")]
    [Ensures("x > 1")]
    [Conditional("PAL")]
    public static void BigPos(int x) { }

    [Requires("Big(x)")]
    [Ensures("Result > 0")]
    [OpaqueSpecs("Big")]
    [Fuel(0, 0)]
    public static int Halve(int x)
    {
        BigPos(x);
        return x / 2;
    }
}
