using System.Diagnostics;
using PalLang;

// §30. `HashSet<T>.Resize`'s rehash: a loop body whose `if` writes an array element,
// followed by a lemma about the array's new contents (R30.12). `HashSet<T>.Add`:
// `out _` (R30.13). And an object used in a nested block whose arm also declares a
// mutable local, which R30.10 now moves the rest of the block into (F19 no longer bites).
public static class Discard
{
    [Spec]
    public static bool AllZeroBelow(Seq<int> xs, SpecInt n) =>
        n <= xs.Length && Pal.Forall((int j) => Pal.Implies(0 <= j && j < n, xs[j] == 0));

    [Lemma]
    [Requires("0 <= i && i < after.Length && after.Length == before.Length && Discard.AllZeroBelow(before, i) && after[i] == 0")]
    [Requires("Pal.Forall((int j) => Pal.Implies(0 <= j && j < i, after[j] == before[j]))")]
    [Ensures("Discard.AllZeroBelow(after, i + 1)")]
    [Conditional("PAL")]
    private static void Step(Seq<int> before, Seq<int> after, SpecInt i) { }

    [Requires("a.Length > 0")]
    [Ensures("Discard.AllZeroBelow(Contents(a), a.Length)")]
    public static void ZeroNonZero(int[] a)
    {
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(0 <= i && Discard.AllZeroBelow(Pal.Contents(a), i));
            Ghost<Seq<int>> before = Pal.Contents(a);
            if (a[i] != 0)
            {
                a[i] = 0;
            }
            Step(before.Value, Pal.Contents(a), i);
        }
    }

    [Ensures("Result == x && found == (x >= 0)")]
    private static int Probe(int x, out bool found)
    {
        found = x >= 0;
        return x;
    }

    [Ensures("Result == x")]
    public static int ProbeValue(int x) => Probe(x, out _);

    [Requires("x < 100")]
    [Ensures("Result == x + 1")]
    public static int ProbeTwice(int x)
    {
        int y = Probe(x, out _);
        Probe(y, out bool _);
        return y + 1;
    }

    [Ensures("Result == 42")]
    public static int AbandonedInABlock(bool b)
    {
        int answer = 42;
        if (b)
        {
            Counter c = new Counter();
            int ignored = c.Get();
        }
        return answer;
    }
}

[Spec]
public struct CounterModel
{
    public SpecInt Value;
}

[Invariant("0 <= n")]
public sealed class Counter
{
    private int n;

    [Model]
    private CounterModel Model => new CounterModel { Value = n };

    [Spec]
    public SpecInt Value => Model.Value;

    [Ensures("@this.Value == 0")]
    public Counter()
    {
        n = 0;
    }

    [Ensures("Result == @this.Value")]
    public int Get()
    {
        return n;
    }
}
