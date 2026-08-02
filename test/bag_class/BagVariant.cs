using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant detector for R5.12. The same class, written every other way C# allows:
/// members in the opposite order, both fields renamed, <c>this.</c> written out, a
/// <c>for</c> loop where <c>Bag</c> uses <c>while</c>, compound assignment and <c>++</c>
/// where <c>Bag</c> writes the assignment out, an expression-bodied method, and the
/// conditional written as a ternary.
///
/// Modulo binder names the emitted Pulse is the same as <c>Bag</c>'s for <c>Add</c>,
/// <c>Size</c> and — the one that matters here — <c>Fill</c>, whose <c>for</c> loop lowers
/// to exactly the Pulse <c>Bag</c>'s <c>while</c> loop lowers to. If it were not, the
/// emitter would have been fitted to how <c>Bag.cs</c> happens to be written.
///
/// <c>Max</c> is the deliberate exception: a ternary is not a differently-written <c>if</c>
/// statement but a different construct — an expression rather than a statement — and R6.4
/// says so, so its body has a different shape by design. What must still match is the loop
/// around it, and it does.
/// </summary>
[Invariant("count <= store.Length")]
[Invariant("0 <= count")]
public sealed class Tote
{
    [Ensures("Result == @this.Count")]
    public int Size() => this.count;

    [Requires("0 < @this.Count")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < @this.Count, @this.Elems[k] <= Result))")]
    public int Max()
    {
        int best = this.store[0];
        for (int i = 1; i < this.count; i++)
        {
            Pal.Invariant(1 <= i && i <= this.count);
            Pal.Invariant(this.count <= this.store.Length);
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(0 <= k && k < i, this.store[k] <= best)));
            Pal.Decreases(this.count - i);
            best = this.store[i] > best ? this.store[i] : best;
        }
        Pal.Assert(this.count <= this.store.Length);
        return best;
    }

    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count)")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < @this.Count, @this.Elems[k] == v))")]
    public void Fill(int v)
    {
        for (int i = 0; i < this.count; i++)
        {
            Pal.Invariant(0 <= i && i <= this.count);
            Pal.Invariant(this.count <= this.store.Length);
            Pal.Invariant(Pal.Forall((int k) => Pal.Implies(0 <= k && k < i, this.store[k] == v)));
            Pal.Decreases(this.count - i);
            this.store[i] = v;
        }
    }

    [Requires("@this.Count < @this.Capacity")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    [Ensures("@this.Elems[Old(@this.Count)] == v")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < Old(@this.Count), @this.Elems[i] == Old(@this.Elems)[i]))")]
    public void Add(int v)
    {
        this.store[this.count] = v;
        this.count += 1;
    }

    [Requires("0 <= capacity")]
    [Ensures("@this.Count == 0")]
    [Ensures("@this.Capacity == capacity")]
    public Tote(int capacity)
    {
        this.store = new int[capacity];
        this.count = 0;
    }

    [Spec]
    public SpecInt Capacity => this.Model.Capacity;

    [Spec]
    public SpecInt Count => this.Model.Elems.Length;

    [Spec]
    public Seq<int> Elems => this.Model.Elems;

    [Refine("Result.Elems.Length <= Result.Capacity")]
    [Model]
    private BagModel Model => new BagModel
    {
        Elems = Pal.Slice(Pal.Contents(this.store), 0, this.count),
        Capacity = this.store.Length,
    };

    private int count;
    private int[] store;
}
