using PalLang;

namespace PalCSharp.Tests;

[Spec]
public struct BagModel
{
    public Seq<int> Elems;
    public SpecInt Capacity;
}

/// <summary>
/// R5.12: a loop inside an instance method.
///
/// The interesting part is what the loop invariant has to own. R4.10 opens the object's
/// invariant across the whole body, so inside the loop the receiver is not an object but a
/// <em>representation</em> — a <c>Box</c> holding the record, plus one array per array
/// field — and those are the resources the loop carries. The emitter supplies them, as
/// R5.8 has always supplied a loop's resources; the propositions are the user's, written
/// against the fields, because inside the window the fields are what there is.
///
/// The class's own <c>[Invariant]</c> clauses are deliberately <em>not</em> carried. They
/// may be transiently false — that is what the window is for — so a loop that needs
/// <c>n &lt;= items.Length</c> says so, and the one below does.
/// </summary>
[Invariant("0 <= n")]
[Invariant("n <= items.Length")]
public sealed class Bag
{
    private int[] items;
    private int n;

    [Refine("Result.Elems.Length <= Result.Capacity")]
    [Model]
    private BagModel Model => new BagModel
    {
        Elems = Pal.Slice(Pal.Contents(items), 0, n),
        Capacity = items.Length,
    };

    [Spec]
    public Seq<int> Elems => Model.Elems;

    [Spec]
    public SpecInt Count => Model.Elems.Length;

    [Spec]
    public SpecInt Capacity => Model.Capacity;

    [Requires("0 <= capacity")]
    [Ensures("@this.Count == 0")]
    [Ensures("@this.Capacity == capacity")]
    public Bag(int capacity)
    {
        items = new int[capacity];
        n = 0;
    }

    [Requires("@this.Count < @this.Capacity")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    [Ensures("@this.Elems[Old(@this.Count)] == v")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < Old(@this.Count), @this.Elems[i] == Old(@this.Elems)[i]))")]
    public void Add(int v)
    {
        items[n] = v;
        n = n + 1;
    }

    /// <summary>
    /// A loop that writes into the array the object owns. It changes the contents but not
    /// the record, so R5.12 quantifies the contents existentially and leaves the record
    /// named from before the loop — which is why <c>n</c> and <c>items.Length</c> may be
    /// mentioned in the measure and are stable across iterations without anyone saying so.
    /// </summary>
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count)")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < @this.Count, @this.Elems[k] == v))")]
    public void Fill(int v)
    {
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i && i <= n);
            Pal.Invariant(n <= items.Length);
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(0 <= k && k < i, items[k] == v)));
            Pal.Decreases(n - i);
            items[i] = v;
            i = i + 1;
        }
    }

    /// <summary>
    /// A loop that reads. The method assigns no field, so R4.11 gives it <c>preserves</c>
    /// and R4.11a re-folds at the model it was handed — which only works because R5.12
    /// names the whole representation before the loop rather than quantifying it. An
    /// existentially quantified record could not possibly abstract to the model the
    /// caller is holding.
    /// </summary>
    [Requires("0 < @this.Count")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < @this.Count, @this.Elems[k] <= Result))")]
    public int Max()
    {
        int best = items[0];
        int i = 1;
        while (i < n)
        {
            Pal.Invariant(1 <= i && i <= n);
            Pal.Invariant(n <= items.Length);
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(0 <= k && k < i, items[k] <= best)));
            Pal.Decreases(n - i);
            if (items[i] > best)
            {
                best = items[i];
            }
            i = i + 1;
        }
        Pal.Assert(n <= items.Length);
        return best;
    }

    [Ensures("Result == @this.Count")]
    public int Size()
    {
        return n;
    }
}
