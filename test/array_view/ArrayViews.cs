using System;
using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §17. `Span&lt;T&gt;` and `ReadOnlySpan&lt;T&gt;` as what they are: borrowed windows.
///
/// A span translates to `Pulse.Lib.Slice.slice` (R17.1), so a method that takes one takes
/// a window of somebody else's memory, at somebody else's offset — and a caller that has
/// an array can hand over the whole of it, or a part.
///
/// The borrow is where the interest is. Creating a span consumes the parent's ownership
/// (R17.5); `Pal.Restore` gives it back (R17.6), and the parent then holds `Pal.Splice` of
/// what it lent out (R17.8). Nothing infers where the borrow ends: the author writes it,
/// exactly as they write every other proof step, and forgetting it fails to verify rather
/// than verifying something false.
/// </summary>
public static class ViewSpec
{
    /// <summary>
    /// Everything below `n` is zero. Stated as a named `[Spec]` predicate rather than as an
    /// inline `Forall` because a loop invariant over a span cannot use a lambda at all: C#
    /// refuses a `ref struct` inside one (CS9108). Naming the predicate moves
    /// `Contents(a)` out of the lambda and into an ordinary argument position, where it is
    /// legal, and the quantifier lives over the `Seq&lt;int&gt;` instead of over the span.
    /// §17.7.
    /// </summary>
    [Spec]
    public static bool ZeroBelow(Seq<int> s, SpecInt n) =>
        Pal.Forall((int k) => Pal.Implies(0 <= k && k < n && k < s.Length, s[k] == 0));
}

public static class ArrayViews
{
    /// <summary>
    /// A writable span. The postcondition is the definition of "cleared", not a weaker
    /// structural property: every cell, not just some.
    /// </summary>
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < Contents(a).Length, Contents(a)[k] == 0))")]
    public static void Clear(Span<int> a)
    {
        int n = a.Length;
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(n == Pal.Contents(a).Length);
            Pal.Invariant(0 <= i && i <= n);
            Pal.Invariant(ViewSpec.ZeroBelow(Pal.Contents(a), i));
            Pal.Decreases(n - i);
            a[i] = 0;
            i++;
        }
    }

    /// <summary>
    /// A read-only span. No `[Frac]` is written, and none is needed: R17.2 reads the
    /// permission off the C# type, which already says the parameter is not written.
    /// </summary>
    [Requires("0 <= i && i < Contents(a).Length")]
    [Ensures("Result == Contents(a)[i]")]
    public static int Read(ReadOnlySpan<int> a, int i) => a[i];

    /// <summary>
    /// Two read-only spans that may be the same memory. Sharing is what a fraction buys,
    /// and R17.2 gives each parameter its own permission, so the caller may pass one array
    /// twice.
    /// </summary>
    [Requires("Contents(a).Length > 0 && Contents(b).Length > 0")]
    [Ensures("Result == (Contents(a)[0] == Contents(b)[0])")]
    public static bool FirstsAgree(ReadOnlySpan<int> a, ReadOnlySpan<int> b) => a[0] == b[0];

    /// <summary>
    /// Bounds are R6.4's, unchanged: the subscript obligations are generated at `a[i]` and
    /// `a[j]` exactly as they would be on an `int[]`.
    /// </summary>
    [Requires("0 <= i && i < Contents(a).Length")]
    [Requires("0 <= j && j < Contents(a).Length")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("Contents(a)[i] == Old(Contents(a))[j]")]
    [Ensures("Contents(a)[j] == Old(Contents(a))[i]")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < Contents(a).Length && k != i && k != j, " +
             "Contents(a)[k] == Old(Contents(a))[k]))")]
    public static void Swap(Span<int> a, int i, int j)
    {
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }

    // -- Borrowing --------------------------------------------------------

    /// <summary>
    /// The implicit `T[]` to `Span&lt;T&gt;` conversion: the whole array, borrowed and
    /// given back. `Pal.Restore` is the only line here that is not ordinary C#, and it is
    /// what makes the postcondition — which is about `a`, not about `s` — provable at all.
    /// </summary>
    [Requires("Contents(a).Length > 0")]
    [Ensures("Contents(a).Length > 0 && Contents(a)[0] == 0")]
    public static void ClearArray(int[] a)
    {
        Span<int> s = a;
        Clear(s);
        Pal.Restore(s);
    }

    /// <summary>The same borrow, spelled with `AsSpan()`, into the read-only row.</summary>
    [Requires("Contents(a).Length > 0")]
    [Ensures("Contents(a).Length > 0 && Result == Contents(a)[0]")]
    public static int FirstOfArray(int[] a)
    {
        ReadOnlySpan<int> s = a.AsSpan();
        int x = Read(s, 0);
        Pal.Restore(s);
        return x;
    }

    /// <summary>
    /// A *window*, which is the whole point of a span and the thing an array cannot do.
    /// `Clear` is written once, over a span, and applies to any contiguous part of any
    /// array — here `[from, from + count)`.
    ///
    /// The postcondition says precisely what happened: the window is zero and everything
    /// outside it is untouched. Both come out of `Pal.Splice`, which is what `a` holds once
    /// the borrow is over (R17.8).
    /// </summary>
    [Requires("0 <= from && 0 <= count && from + count <= Contents(a).Length")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("Forall((int k) => Implies(from <= k && k < from + count, Contents(a)[k] == 0))")]
    [Ensures("Forall((int k) => Implies(0 <= k && k < Contents(a).Length && " +
             "(k < from || from + count <= k), Contents(a)[k] == Old(Contents(a))[k]))")]
    public static void ClearRange(int[] a, int from, int count)
    {
        Span<int> w = a.AsSpan(from, count);
        Clear(w);
        Pal.Restore(w);
    }

    /// <summary>
    /// A window of a window, given back innermost first. The outer receipt cannot be
    /// redeemed before the inner one, because it is the inner span that is holding the
    /// ownership the outer one needs — which is not a rule anybody wrote down, just what
    /// the resources say.
    /// </summary>
    [Requires("2 <= Contents(a).Length")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("Contents(a).Length > 1 && Contents(a)[1] == 7")]
    public static void SetSecond(int[] a)
    {
        Span<int> outer = a.AsSpan(0, 2);
        Span<int> inner = outer.Slice(1, 1);
        inner[0] = 7;
        Pal.Restore(inner);
        Pal.Restore(outer);
    }

    /// <summary>
    /// A read-only window given back unwritten leaves the array exactly as it was, which is
    /// `splice_same` in `Pulse.Lib.CSharp.Seq` — so a read-only borrow costs its user
    /// nothing beyond the bounds.
    /// </summary>
    [Requires("0 <= from && from < Contents(a).Length")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("Contents(a).Length > from && from >= 0 && Result == Contents(a)[from]")]
    public static int ReadAt(int[] a, int from)
    {
        ReadOnlySpan<int> w = a.AsSpan(from, 1);
        int x = Read(w, 0);
        Pal.Restore(w);
        return x;
    }

    /// <summary>
    /// Range syntax, `s[i..j]`, which borrows exactly as `s.Slice(i, j - i)` does — the two
    /// spellings translate identically, which is what §0's structure-preservation rule
    /// requires of two spellings of one operation.
    /// </summary>
    [Requires("3 <= Contents(a).Length")]
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("Contents(a).Length > 2 && Contents(a)[2] == 9")]
    public static void SetThird(int[] a)
    {
        Span<int> s = a;
        Span<int> w = s[1..3];
        w[1] = 9;
        Pal.Restore(w);
        Pal.Restore(s);
    }
}
