using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The §7.2 variant: the same three theorems, written differently. The type argument is
/// written out rather than inferred, the locals are fewer and named differently, the
/// element indices are computed rather than literal, and the composition goes through a
/// generic helper the original does not have. No emitter change may be needed.
/// </summary>
public static class Interchanging
{
    /// <summary>
    /// A generic `[Lemma]`: writing a cell's own value back changes nothing. General over
    /// the element type, because at an unconstrained `T` there is nothing else it could be.
    /// </summary>
    [Lemma]
    [Requires("0 <= p && p < s.Length")]
    [Ensures("SetAt(s, p, s[p]) == s")]
    [System.Diagnostics.Conditional("PAL")]
    public static void WriteBackIsNoOp<T>(Seq<T> s, int p) { }

    [Requires("0 <= p && p < a.Length")]
    [Requires("0 <= q && q < a.Length")]
    [Ensures("Contents(a) == SetAt(SetAt(Old(Contents(a)), p, Old(Contents(a))[q]), q, Old(Contents(a))[p])")]
    public static void Interchange<T>(T[] a, int p, int q)
    {
        T held = a[p];
        WriteBackIsNoOp<T>(Pal.Contents(a), p);
        a[p] = a[q];
        a[q] = held;
    }

    /// <summary>
    /// A generic helper the original has no analogue of, interposed between the two
    /// levels of the composition.
    /// </summary>
    [Requires("0 <= p && p < a.Length")]
    [Requires("0 <= q && q < a.Length")]
    [Ensures("Contents(a) == SetAt(SetAt(Old(Contents(a)), p, Old(Contents(a))[q]), q, Old(Contents(a))[p])")]
    public static void InterchangeVia<T>(T[] a, int p, int q)
    {
        Interchange<T>(a, p, q);
    }

    [Requires("2 <= a.Length")]
    [Ensures("Contents(a) == SetAt(SetAt(Old(Contents(a)), 0, Old(Contents(a))[Old(Contents(a)).Length - 1]), Old(Contents(a)).Length - 1, Old(Contents(a))[0])")]
    public static void InterchangeEnds<T>(T[] a)
    {
        int last = a.Length - 1;
        InterchangeVia<T>(a, 0, last);
    }

    [Requires("2 <= a.Length")]
    [Ensures("Contents(a) == SetAt(SetAt(Old(Contents(a)), 0, Old(Contents(a))[Old(Contents(a)).Length - 1]), Old(Contents(a)).Length - 1, Old(Contents(a))[0])")]
    public static void InterchangeEndsOfLongs(long[] a)
    {
        InterchangeEnds<long>(a);
    }
}
