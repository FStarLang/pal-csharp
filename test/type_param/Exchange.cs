using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Unconstrained generics (doc/translation.md §14). None of these methods can look at
/// an element: a type parameter with no constraint admits no operation but moving the
/// value around. That is exactly why the specification can be complete — the resulting
/// sequence is determined by the input sequence, with no arithmetic in sight.
/// </summary>
public static class Exchanging
{
    /// <summary>
    /// The sequence `s` with positions `i` and `j` interchanged. A generic specification
    /// function: `T` is in scope in the signature, in the body and — through R14.2b — in
    /// the specification strings of every method that names it.
    /// </summary>
    [Spec]
    [Requires("0 <= i && i < s.Length && 0 <= j && j < s.Length")]
    public static Seq<T> Interchanged<T>(Seq<T> s, int i, int j) =>
        Pal.SetAt(Pal.SetAt(s, i, s[j]), j, s[i]);

    /// <summary>
    /// Interchange two elements. The postcondition names the *whole* result sequence,
    /// so it says what the method computes, not merely that the two positions moved.
    /// </summary>
    [Requires("0 <= i && i < a.Length")]
    [Requires("0 <= j && j < a.Length")]
    [Ensures("Contents(a) == Interchanged(Old(Contents(a)), i, j)")]
    public static void Exchange<T>(T[] a, int i, int j)
    {
        T x = a[i];
        T y = a[j];
        a[i] = y;
        a[j] = x;
    }

    /// <summary>
    /// A generic method calling a generic method, passing its own type parameter along.
    /// This is the composition fact (F64): instantiation is ordinary application, so no
    /// monomorphising pass is needed.
    /// </summary>
    [Requires("2 <= a.Length")]
    [Ensures("Contents(a) == SetAt(SetAt(Old(Contents(a)), 0, Old(Contents(a))[Old(Contents(a)).Length - 1]), Old(Contents(a)).Length - 1, Old(Contents(a))[0])")]
    public static void ExchangeEnds<T>(T[] a)
    {
        Exchange(a, 0, a.Length - 1);
    }

    /// <summary>
    /// A non-generic caller instantiating at a concrete type. Roslyn resolved the type
    /// argument here by inference; R14.5 emits it explicitly all the same.
    /// </summary>
    [Requires("2 <= a.Length")]
    [Ensures("Contents(a) == SetAt(SetAt(Old(Contents(a)), 0, Old(Contents(a))[Old(Contents(a)).Length - 1]), Old(Contents(a)).Length - 1, Old(Contents(a))[0])")]
    public static void ExchangeEndsOfBytes(byte[] a)
    {
        ExchangeEnds(a);
    }
}
