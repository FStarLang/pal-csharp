using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant detector, for a class that owns a resource. This is <c>Stack</c>
/// rewritten in every way C# allows without changing what it means: members in the
/// opposite order, different field and model-field names, <c>this.</c> written out,
/// <c>++</c>/<c>--</c> instead of assignment, expression bodies where they fit, and the
/// model's two fields initialised the other way round.
///
/// The emitted Pulse must be identical to <c>Stack</c>'s modulo those names. Anything
/// else means the translation is reading the way the source was written rather than what
/// it says — which is the failure mode §0 exists to prevent, and the one that no amount
/// of "the tests pass" would otherwise reveal.
/// </summary>
[Spec]
public struct PileModel
{
    public Seq<int> Values;
    public SpecInt Room;
}

[Invariant("0 <= n")]
[Invariant("n <= store.Length")]
public sealed class Pile
{
    [Ensures("Result == @this.Count")]
    public int Size() => this.n;

    [Requires("0 < @this.Count")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) - 1")]
    [Ensures("Result == Old(@this.Elems)[Old(@this.Count) - 1]")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < @this.Count, @this.Elems[i] == Old(@this.Elems)[i]))")]
    public int Pop()
    {
        this.n--;
        return this.store[this.n];
    }

    [Requires("@this.Count < @this.Capacity")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    [Ensures("@this.Elems[Old(@this.Count)] == v")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < Old(@this.Count), @this.Elems[i] == Old(@this.Elems)[i]))")]
    public void Push(int v)
    {
        this.store[this.n] = v;
        this.n++;
    }

    [Requires("0 <= capacity")]
    [Ensures("@this.Count == 0")]
    [Ensures("@this.Capacity == capacity")]
    public Pile(int capacity)
    {
        this.store = new int[capacity];
        this.n = 0;
    }

    [Spec]
    public SpecInt Capacity => this.Model.Room;

    [Spec]
    public SpecInt Count => this.Model.Values.Length;

    [Spec]
    public Seq<int> Elems => this.Model.Values;

    [Refine("Result.Values.Length <= Result.Room")]
    [Model]
    private PileModel Model => new PileModel
    {
        Values = Pal.Slice(Pal.Contents(this.store), 0, this.n),
        Room = this.store.Length,
    };

    private int n;
    private int[] store;
}
