using PalLang;

namespace PalCSharp.Tests;

/// <summary>The model of a queue: what is in it, and how much it will hold.</summary>
[Spec]
public struct RingModel
{
    public Seq<int> Elems;
    public SpecInt Capacity;
}

/// <summary>
/// <c>test/circular_buffer</c>, done right.
///
/// That test is M1's, and M1 has no way to hide anything: the buffer is a struct, the
/// storage is a separate <c>int[]</c> the caller has to carry alongside it, and every
/// specification is written against <c>head</c>, <c>count</c> and raw indices — the
/// caller reasons about the layout because there is nothing else to reason about.
///
/// Here the layout is private. R3.10a puts the array's <c>A.pts_to</c> inside the object
/// invariant, so <c>buf</c>, <c>head</c> and <c>count</c> are unreachable from outside,
/// and R3.9's model says the only thing a client should know: this is a queue of
/// <c>Elems</c> with room for <c>Capacity</c>. The wrap-around is a fact about the
/// abstraction function and nowhere else.
///
/// The abstraction function is <c>Pal.Rotate</c>: the contents read from <c>head</c>,
/// wrapping, truncated to <c>count</c>. Its characteristic equation
/// (<c>Rotate(s, n)[k] == s[(n + k) % s.Length]</c>) and the two modular facts that make a
/// moving origin sound live in <c>Pulse.Lib.CSharp.Seq</c>, stated over arbitrary
/// sequences — §0 rule 3's second sanctioned home for proof difficulty.
/// </summary>
/// <remarks>
/// The capacity bound is R6.4, not decoration. <c>Enqueue</c> computes <c>head + count</c>
/// at machine width; <c>head &lt; buf.Length</c> and <c>count &lt;= buf.Length</c> alone
/// bound that by <c>2 * buf.Length</c>, which overflows. Halving the admissible capacity
/// is the honest fix, and it belongs on the class because it is a fact about the fields.
/// </remarks>
[Invariant("0 <= head")]
[Invariant("head < buf.Length")]
[Invariant("0 <= count")]
[Invariant("count <= buf.Length")]
[Invariant("buf.Length <= 1073741823")]
public sealed class RingBuffer
{
    private int[] buf;
    private int head;
    private int count;

    [Refine("Result.Elems.Length <= Result.Capacity")]
    [Model]
    private RingModel Model => new RingModel
    {
        Elems = Pal.Slice(Pal.Rotate(Pal.Contents(buf), head), 0, count),
        Capacity = buf.Length,
    };

    [Spec]
    public Seq<int> Elems => Model.Elems;

    [Spec]
    public SpecInt Count => Model.Elems.Length;

    [Spec]
    public SpecInt Capacity => Model.Capacity;

    /// <summary>
    /// A ring buffer with no storage has no origin to point at, so the capacity is
    /// strictly positive. That is R3.11: the constructor is where a class invariant is
    /// first established, and anything the invariant needs but cannot derive has to be
    /// asked of the caller.
    /// </summary>
    [Requires("0 < capacity")]
    [Requires("capacity <= 1073741823")]
    [Ensures("@this.Count == 0")]
    [Ensures("@this.Capacity == capacity")]
    public RingBuffer(int capacity)
    {
        buf = new int[capacity];
        head = 0;
        count = 0;
    }

    /// <summary>
    /// The write lands one past the end of the window, wrapped. Nothing already in the
    /// queue moves — which is the whole reason to write a queue this way, and which the
    /// element-wise postcondition states.
    /// </summary>
    [Requires("@this.Count < @this.Capacity")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    [Ensures("@this.Elems[Old(@this.Count)] == v")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < Old(@this.Count), @this.Elems[i] == Old(@this.Elems)[i]))")]
    public void Enqueue(int v)
    {
        int slot = head + count;
        if (slot >= buf.Length)
        {
            slot = slot - buf.Length;
        }
        buf[slot] = v;
        count = count + 1;
    }

    /// <summary>
    /// The origin moves and the stored bytes do not. So the invariant is broken twice
    /// over between the first assignment and the last — after <c>head = head + 1</c> it
    /// may be out of range, and until <c>count</c> catches up the window covers a cell
    /// that has been dropped — and R3.10's <c>pure</c> conjunct is what lets it be.
    /// </summary>
    [Requires("0 < @this.Count")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) - 1")]
    [Ensures("Result == Old(@this.Elems)[0]")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < @this.Count, @this.Elems[i] == Old(@this.Elems)[i + 1]))")]
    public int Dequeue()
    {
        int v = buf[head];
        head = head + 1;
        if (head >= buf.Length)
        {
            head = head - buf.Length;
        }
        count = count - 1;
        return v;
    }

    [Ensures("Result == @this.Count")]
    public int Size()
    {
        return count;
    }

    [Ensures("Iff(Result, @this.Count == @this.Capacity)")]
    public bool IsFull()
    {
        return count == buf.Length;
    }
}
