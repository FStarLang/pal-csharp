using PalLang;

// R24.14: a `return` inside a loop, which is how `HashSet<T>.FindItemIndex` and `Remove` leave
// their chain walks. R24.12: a ghost local.
public static class Search
{
    [Ensures("-1 <= Result && Result < a.Length")]
    [Ensures("Result < 0 || Contents(a)[Result] == x")]
    [Ensures("Result >= 0 || Pal.Forall((int k) => Pal.Implies(0 <= k && k < a.Length, Contents(a)[k] != x))")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    public static int Find(int[] a, int x)
    {
        int i = 0;
        while (i < a.Length)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(0 <= k && k < i, Pal.Contents(a)[k] != x)));
            Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<int>() == i && i < a.Length && Pal.Contents(a)[i] == x));
            Pal.Decreases(a.Length - i);
            if (a[i] == x) return i;
            i++;
        }
        return -1;
    }

    // The loop is inside an `if` that something follows, and the method returns `bool`.
    [Ensures("Result == (a.Length > 0 && Pal.Exists((int k) => 0 <= k && k < a.Length && Contents(a)[k] == x))")]
    public static bool Has(int[] a, int x)
    {
        if (a.Length > 0)
        {
            for (int i = 0; i < a.Length; i++)
            {
                Pal.Invariant(0 <= i && i <= a.Length);
                Pal.Invariant(Pal.Forall((int k) => Pal.Implies(0 <= k && k < i, Pal.Contents(a)[k] != x)));
                Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && i < a.Length && Pal.Contents(a)[i] == x));
                if (a[i] == x)
                {
                    return true;
                }
            }
        }
        return false;
    }

    // R24.12: a snapshot of the contents, named by a later assertion.
    [Requires("a.Length > 0")]
    [Ensures("Contents(a) == Pal.SetAt(Old(Contents(a)), 0, v)")]
    public static void SetFirst(int[] a, int v)
    {
        Ghost<Seq<int>> before = Pal.Contents(a);
        a[0] = v;
        Pal.Assert(Pal.Contents(a) == Pal.SetAt(before.Value, 0, v));
    }
}
