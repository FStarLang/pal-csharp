using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant detector, applied to the hardest thing in M2: a class whose abstraction
/// function has a moving origin. This is <c>RingBuffer</c> rewritten in every way C#
/// allows without changing what it means — members in the opposite order, different field
/// and model-field names, <c>this.</c> written out, compound assignment instead of
/// assignment, expression bodies where they fit, and the model's fields initialised the
/// other way round.
///
/// The emitted Pulse must be identical to <c>RingBuffer</c>'s modulo those names. If
/// wrap-around had been recognised as a shape rather than translated as arithmetic, this
/// is where it would show.
/// </summary>
[Spec]
public struct QueueModel
{
    public SpecInt Room;
    public Seq<int> Items;
}

[Invariant("0 <= start")]
[Invariant("start < store.Length")]
[Invariant("0 <= used")]
[Invariant("used <= store.Length")]
[Invariant("store.Length <= 1073741823")]
public sealed class Queue
{
    [Ensures("Iff(Result, @this.Capacity == @this.Count)")]
    public bool IsFull() => this.used == this.store.Length;

    [Ensures("Result == @this.Count")]
    public int Size() => this.used;

    [Requires("0 < @this.Count")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) - 1")]
    [Ensures("Result == Old(@this.Elems)[0]")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < @this.Count, @this.Elems[k] == Old(@this.Elems)[k + 1]))")]
    public int Dequeue()
    {
        int taken = this.store[this.start];
        this.start += 1;
        if (this.start >= this.store.Length)
        {
            this.start -= this.store.Length;
        }
        this.used -= 1;
        return taken;
    }

    [Requires("@this.Count < @this.Capacity")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    [Ensures("@this.Elems[Old(@this.Count)] == item")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < Old(@this.Count), @this.Elems[k] == Old(@this.Elems)[k]))")]
    public void Enqueue(int item)
    {
        int where = this.start + this.used;
        if (where >= this.store.Length)
        {
            where -= this.store.Length;
        }
        this.store[where] = item;
        this.used += 1;
    }

    [Requires("0 < room")]
    [Requires("room <= 1073741823")]
    [Ensures("@this.Count == 0")]
    [Ensures("@this.Capacity == room")]
    public Queue(int room)
    {
        this.store = new int[room];
        this.start = 0;
        this.used = 0;
    }

    [Spec]
    public SpecInt Capacity => Model.Room;

    [Spec]
    public SpecInt Count => Model.Items.Length;

    [Spec]
    public Seq<int> Elems => Model.Items;

    [Refine("Result.Items.Length <= Result.Room")]
    [Model]
    private QueueModel Model => new QueueModel
    {
        Room = this.store.Length,
        Items = Pal.Slice(Pal.Rotate(Pal.Contents(this.store), this.start), 0, this.used),
    };

    private int used;
    private int start;
    private int[] store;
}
