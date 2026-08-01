using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The state of a circular buffer: where the live data starts, and how much of it
/// there is. The storage is deliberately <em>not</em> a field.
///
/// <para>
/// A C# <c>struct</c> is a value, so assigning one copies it. If this type held the
/// <c>int[]</c>, every copy would be a second owner of the same memory — precisely the
/// aliasing separation logic exists to rule out — and the translator rejects it
/// (PALCS0511). PAL can put a pointer in a C struct because a C struct is addressed,
/// not copied. So the storage travels alongside the state, which is also how the
/// buffer's owner already has to think about it.
/// </para>
/// </summary>
[Refine("0 <= Head && 0 <= Count")]
public struct RingState
{
    /// <summary>Index of the oldest live element.</summary>
    public int Head;

    /// <summary>Number of live elements.</summary>
    public int Count;
}

public static class Ring
{
    /// <summary>
    /// The invariant relating a state to its storage. Every operation requires it and
    /// re-establishes it, which is what makes the index arithmetic below in bounds.
    ///
    /// <para>
    /// The bound on <paramref name="capacity"/> is not decoration: pal-csharp holds a
    /// C# <c>int</c> to its declared range, so <c>Head + Count</c> must be shown not to
    /// overflow. Half the range is the weakest bound that makes every sum below fit.
    /// </para>
    /// </summary>
    [Spec]
    public static bool Fits(RingState s, int capacity) =>
        0 < capacity && capacity <= 1073741823 && s.Head < capacity && s.Count <= capacity;

    /// <summary>
    /// Where the <c>i</c>th live element sits in physical storage — as a pure function,
    /// so that specifications can say it. This is the whole content of "circular": the
    /// wrap is what turns a linear index into a physical one.
    /// </summary>
    [Spec]
    public static int At(int start, int i, int capacity) =>
        start + i < capacity ? start + i : start + i - capacity;

    /// <summary>
    /// The executable counterpart. Its postcondition is what connects it to the model:
    /// without <c>Result == At(...)</c> a caller would learn only that the index is in
    /// range, which is a type property rather than the correctness property.
    /// </summary>
    [Requires("0 <= i && i <= capacity")]
    [Requires("0 <= start && start < capacity")]
    [Requires("capacity <= 1073741823")]
    [Ensures("Result == At(start, i, capacity)")]
    [Ensures("0 <= Result && Result < capacity")]
    public static int Wrap(int start, int i, int capacity)
    {
        int raw = start + i;
        if (raw >= capacity)
        {
            return raw - capacity;
        }
        return raw;
    }

    /// <summary>
    /// Append a value. The slot written is one past the last live element, wrapped.
    /// </summary>
    [Requires("Fits(s, a.Length)")]
    [Requires("s.Count < a.Length")]
    [Ensures("Fits(s, a.Length)")]
    [Ensures("s.Head == Old(s.Head)")]
    [Ensures("s.Count == Old(s.Count) + 1")]
    [Ensures("a[At(Old(s.Head), Old(s.Count), a.Length)] == value")]
    public static void Enqueue(int[] a, ref RingState s, int value)
    {
        int at = Wrap(s.Head, s.Count, a.Length);
        a[at] = value;
        s.Count = s.Count + 1;
    }

    /// <summary>
    /// Remove and return the oldest value. The head advances by one, wrapped; the
    /// storage is left untouched, which the postcondition states rather than leaving
    /// the caller to guess.
    /// </summary>
    [Requires("Fits(s, a.Length)")]
    [Requires("s.Count > 0")]
    [Ensures("a.Length == Old(a.Length)")]
    [Ensures("Fits(s, a.Length)")]
    [Ensures("Result == Old(a[s.Head])")]
    [Ensures("s.Head == At(Old(s.Head), 1, a.Length)")]
    [Ensures("s.Count == Old(s.Count) - 1")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < a.Length, a[k] == Old(a[k])))")]
    public static int Dequeue(int[] a, ref RingState s)
    {
        int value = a[s.Head];
        s.Head = Wrap(s.Head, 1, a.Length);
        s.Count = s.Count - 1;
        return value;
    }

    /// <summary>
    /// Fill an empty buffer completely. The loop invariant carries the state's relation
    /// to the storage across iterations, since a Pulse loop body sees the invariant and
    /// nothing else.
    /// </summary>
    [Requires("Fits(s, a.Length)")]
    [Requires("s.Count == 0")]
    [Ensures("Fits(s, a.Length)")]
    [Ensures("s.Count == a.Length")]
    public static void FillAll(int[] a, ref RingState s, int value)
    {
        while (s.Count < a.Length)
        {
            Pal.Invariant(Fits(s, a.Length));
            Pal.Invariant(s.Count <= a.Length);
            Pal.Decreases(a.Length - s.Count);
            Enqueue(a, ref s, value);
        }
    }
}
