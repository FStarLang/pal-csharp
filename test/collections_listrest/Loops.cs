using System;
using PalLang;

// §26. Loops: `break` in an invariant, guards that write, a mutable pair, and an array
// field written through a local alias.
public static class Loops
{
    // R26.10. `Pal.Broke()` says why the loop ended.
    [Ensures("Pal.Implies(Result >= 0, Result < items.Length && Pal.Contents(items)[Result] == x)")]
    public static int IndexOf(int[] items, int x)
    {
        int i = 0;
        while (i < items.Length)
        {
            Pal.Invariant(0 <= i && i <= items.Length);
            Pal.Invariant(Pal.Implies(Pal.Broke(), i < items.Length && Pal.Contents(items)[i] == x));
            Pal.Decreases(items.Length - i);
            if (items[i] == x)
            {
                break;
            }
            i++;
        }
        return i < items.Length ? i : -1;
    }

    // R26.11. `++i` in the guard: the invariant describes the state after it.
    [Requires("0 <= start && start <= items.Length")]
    [Ensures("start <= Result && Result <= items.Length")]
    [Ensures("Pal.Implies(Result < items.Length, Pal.Contents(items)[Result] != 0)")]
    public static int SkipZeros(int[] items, int start)
    {
        int i = start - 1;
        while (++i < items.Length)
        {
            Pal.Invariant(start <= i && i <= items.Length);
            Pal.Invariant(Pal.Implies(Pal.Broke(), i < items.Length && Pal.Contents(items)[i] != 0));
            Pal.Decreases(items.Length - i);
            if (items[i] != 0)
            {
                break;
            }
        }
        return i;
    }

    // R26.11. `(j = e) < n` in the guard.
    [Requires("0 <= n && n <= 1000")]
    [Ensures("Result == 2 * n")]
    public static int Doubles(int n)
    {
        int k = 0;
        int j;
        while ((j = 2 * k) < 2 * n)
        {
            Pal.Invariant(0 <= k && k <= n && j == 2 * k);
            Pal.Decreases(n - k);
            k++;
        }
        return j;
    }

    // R26.8. A pair held in a mutable local.
    [Requires("nodes.Length > 0")]
    [Ensures("Pal.Same(Result, Pal.Old(Pal.Contents(nodes))[Pal.Old(Pal.Contents(nodes)).Length - 1])")]
    public static (TE, TP) Last<TE, TP>((TE, TP)[] nodes)
    {
        (TE, TP) last = nodes[0];
        for (int i = 1; i < nodes.Length; i++)
        {
            Pal.Invariant(1 <= i && i <= nodes.Length);
            Pal.Invariant(Pal.Same(last, Pal.Contents(nodes)[i - 1]));
            last = nodes[i];
        }
        return last;
    }
}

[Spec]
public struct ZeroerModel
{
    public Seq<int> Items;
}

public class Zeroer
{
    private int[] _items;

    [Model]
    private ZeroerModel Model => new ZeroerModel { Items = Pal.Contents(_items) };

    [Spec]
    public Seq<int> Items => Model.Items;

    [Requires("0 <= n")]
    [Ensures("@this.Items.Length == n")]
    public Zeroer(int n)
    {
        _items = new int[n];
    }

    // R26.10. Writing an array field's elements through a local alias of it.
    [Ensures("@this.Items.Length == Pal.Old(@this.Items).Length")]
    [Ensures("Pal.Forall((SpecInt k) => Pal.Implies(0 <= k && k < @this.Items.Length, @this.Items[k] == 0))")]
    public void Clear()
    {
        int[] items = _items;
        int i = 0;
        while (i < items.Length)
        {
            Pal.Invariant(0 <= i && i <= Pal.Contents(_items).Length);
            Pal.Invariant(Pal.Forall((SpecInt k) => Pal.Implies(0 <= k && k < i, Pal.Contents(_items)[k] == 0)));
            Pal.Decreases(items.Length - i);
            items[i] = 0;
            i++;
        }
    }
}
