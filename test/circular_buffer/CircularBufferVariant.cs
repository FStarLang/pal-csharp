using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// An equivalent circular buffer, written differently (doc/translation.md §0). It must
/// verify with no change to the translator.
///
/// <para>
/// What differs: the state is an auto-property struct with the fields in the opposite
/// order and a field-level <c>[Refine]</c>; the invariant is spelled with an explicit
/// conjunction rather than a chain; contracts are written body-level where a body
/// exists; the wrap is computed by subtracting rather than branching on the sum; the
/// filling loop is a <c>for</c> rather than a <c>while</c>; and <c>Dequeue</c> reads
/// through a local instead of the field. All of that is surface variation the scheme
/// must be blind to.
/// </para>
/// </summary>
public struct RingV
{
    /// <summary>Number of live elements.</summary>
    [Refine("Count >= 0")]
    public int Count { get; set; }

    /// <summary>Index of the oldest live element.</summary>
    [Refine("Head >= 0")]
    public int Head { get; set; }
}

public static class RingVariant
{
    [Spec]
    public static bool Ok(RingV r, int cap) =>
        (0 < cap && cap <= 1073741823) && (r.Head < cap && r.Count <= cap);

    [Spec]
    public static int Slot(int head, int offset, int cap) =>
        head + offset >= cap ? head + offset - cap : head + offset;

    public static int Rotate(int head, int offset, int cap)
    {
        Pal.Requires(0 <= offset && offset <= cap);
        Pal.Requires(0 <= head && head < cap);
        Pal.Requires(cap <= 1073741823);
        Pal.Ensures(Pal.Result<int>() == Slot(head, offset, cap));
        Pal.Ensures(0 <= Pal.Result<int>() && Pal.Result<int>() < cap);

        int sum = head + offset;
        int over = sum - cap;
        if (over >= 0)
        {
            return over;
        }
        return sum;
    }

    [Requires("Ok(r, buf.Length)")]
    [Requires("r.Count < buf.Length")]
    [Ensures("Ok(r, buf.Length)")]
    [Ensures("r.Head == Old(r.Head)")]
    [Ensures("r.Count == Old(r.Count) + 1")]
    [Ensures("buf[Slot(Old(r.Head), Old(r.Count), buf.Length)] == x")]
    public static void Push(int[] buf, ref RingV r, int x)
    {
        int slot = Rotate(r.Head, r.Count, buf.Length);
        buf[slot] = x;
        r.Count = r.Count + 1;
    }

    [Requires("Ok(r, buf.Length)")]
    [Requires("r.Count > 0")]
    [Ensures("buf.Length == Old(buf.Length)")]
    [Ensures("Ok(r, buf.Length)")]
    [Ensures("Result == Old(buf[r.Head])")]
    [Ensures("r.Head == Slot(Old(r.Head), 1, buf.Length)")]
    [Ensures("r.Count == Old(r.Count) - 1")]
    [Ensures("Forall((int n) => Implies(0 <= n && n < buf.Length, buf[n] == Old(buf[n])))")]
    public static int Pop(int[] buf, ref RingV r)
    {
        int head = r.Head;
        int x = buf[head];
        r.Head = Rotate(head, 1, buf.Length);
        r.Count = r.Count - 1;
        return x;
    }

    [Requires("Ok(r, buf.Length)")]
    [Requires("r.Count == 0")]
    [Ensures("Ok(r, buf.Length)")]
    [Ensures("r.Count == buf.Length")]
    public static void Saturate(int[] buf, ref RingV r, int x)
    {
        for (int n = r.Count; n < buf.Length; n = r.Count)
        {
            Pal.Invariant(Ok(r, buf.Length));
            Pal.Invariant(n == r.Count);
            Pal.Invariant(r.Count <= buf.Length);
            Pal.Decreases(buf.Length - r.Count);
            Push(buf, ref r, x);
        }
    }
}
