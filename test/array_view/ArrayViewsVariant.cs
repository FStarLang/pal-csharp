using System;
using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §0's variant test for §17: the same borrowing, written by somebody else.
///
/// Every window here is spelled differently from its counterpart in `ArrayViews.cs` — the
/// one-argument `AsSpan(i)` and `Slice(i)` forms instead of the two-argument ones, range
/// syntax where the original used `Slice` and `Slice` where it used a range, `for` where
/// the original used `while`, a descending loop where the original ascended — and the
/// specifications are worded independently. Nothing in the translator may need to change.
/// </summary>
public static class ViewSpecVariant
{
    /// <summary>Nothing at or above `n` is non-zero. Named, not inlined, because C# will
    /// not let a `ref struct` cross into a lambda (CS9108) — so a loop invariant that
    /// quantifies over a span has to quantify over its `Seq&lt;int&gt;` contents instead.</summary>
    [Spec]
    public static bool AllZeroFrom(Seq<int> xs, SpecInt n) =>
        Pal.Forall((int p) => Pal.Implies(0 <= p && n <= p && p < xs.Length, xs[p] == 0));
}

public static class ArrayViewsVariant
{
    /// <summary>Descending, `for`-shaped, and zeroing the tail rather than the head.</summary>
    [Ensures("Contents(v).Length == Old(Contents(v)).Length")]
    [Ensures("Forall((int p) => Implies(0 <= p && p < Contents(v).Length, Contents(v)[p] == 0))")]
    public static void Wipe(Span<int> v)
    {
        int len = v.Length;
        for (int k = len; k > 0; k--)
        {
            Pal.Invariant(len == Pal.Contents(v).Length);
            Pal.Invariant(0 <= k && k <= len);
            Pal.Invariant(ViewSpecVariant.AllZeroFrom(Pal.Contents(v), k));
            Pal.Decreases(k);
            v[k - 1] = 0;
        }
    }

    [Requires("0 <= p && p < Contents(v).Length")]
    [Ensures("Result == Contents(v)[p]")]
    public static int Peek(ReadOnlySpan<int> v, int p) => v[p];

    [Requires("0 <= p && p < Contents(v).Length")]
    [Ensures("Contents(v).Length == Old(Contents(v)).Length")]
    [Ensures("Contents(v).Length > p && p >= 0 && Result == Contents(v)[p]")]
    public static int PeekSuffix(int[] v, int p)
    {
        ReadOnlySpan<int> whole = v.AsSpan();
        ReadOnlySpan<int> tail = whole.Slice(start: p, length: whole.Length - p);
        int got = tail[0];
        Pal.Restore(tail);
        Pal.Restore(whole);
        return got;
    }

    /// <summary>Two read-only windows, possibly of the same array: each parameter carries
    /// its own fraction (R17.2), so a caller may lend the same memory twice.</summary>
    [Requires("Contents(v).Length > 0 && Contents(w).Length > 0")]
    [Ensures("Result == (Contents(v)[0] <= Contents(w)[0])")]
    public static bool HeadOrdered(ReadOnlySpan<int> v, ReadOnlySpan<int> w) => v[0] <= w[0];

    [Requires("0 <= p && p < Contents(v).Length")]
    [Requires("0 <= q && q < Contents(v).Length")]
    [Ensures("Contents(v).Length == Old(Contents(v)).Length")]
    [Ensures("Contents(v)[p] == Old(Contents(v))[q]")]
    [Ensures("Contents(v)[q] == Old(Contents(v))[p]")]
    [Ensures("Forall((int r) => Implies(0 <= r && r < Contents(v).Length && r != p && r != q, " +
             "Contents(v)[r] == Old(Contents(v))[r]))")]
    public static void Exchange(Span<int> v, int p, int q)
    {
        int held = v[q];
        v[q] = v[p];
        v[p] = held;
    }

    // -- Borrowing --------------------------------------------------------

    /// <summary>Explicit `AsSpan()` where the original relied on the implicit conversion.</summary>
    [Requires("Contents(v).Length > 0")]
    [Ensures("Contents(v).Length > 0 && Contents(v)[0] == 0")]
    public static void WipeAll(int[] v)
    {
        Span<int> whole = v.AsSpan();
        Wipe(whole);
        Pal.Restore(whole);
    }

    /// <summary>Implicit conversion where the original wrote `AsSpan()`.</summary>
    [Requires("Contents(v).Length > 0")]
    [Ensures("Contents(v).Length > 0 && Result == Contents(v)[0]")]
    public static int HeadOf(int[] v)
    {
        ReadOnlySpan<int> whole = v;
        int got = Peek(whole, 0);
        Pal.Restore(whole);
        return got;
    }

    /// <summary>
    /// A suffix, taken with the one-argument `AsSpan(p)` — whose length R17.5 synthesises as
    /// `v.Length - p`, so this must translate exactly as the two-argument form would.
    /// </summary>
    [Requires("0 <= p && p <= Contents(v).Length")]
    [Ensures("Contents(v).Length == Old(Contents(v)).Length")]
    [Ensures("Forall((int r) => Implies(p <= r && r < Contents(v).Length, Contents(v)[r] == 0))")]
    [Ensures("Forall((int r) => Implies(0 <= r && r < p, Contents(v)[r] == Old(Contents(v))[r]))")]
    public static void WipeSuffix(int[] v, int p)
    {
        Span<int> tail = v.AsSpan(p);
        Wipe(tail);
        Pal.Restore(tail);
    }

    /// <summary>
    /// Nested, but taken through range syntax on the outside and `Slice` on the inside —
    /// the mirror image of how the original nested its two windows.
    /// </summary>
    [Requires("2 <= Contents(v).Length")]
    [Ensures("Contents(v).Length == Old(Contents(v)).Length")]
    [Ensures("Contents(v).Length > 1 && Contents(v)[1] == 7")]
    public static void PokeSecond(int[] v)
    {
        Span<int> whole = v;
        Span<int> pair = whole[0..2];
        Span<int> last = pair.Slice(1);
        last[0] = 7;
        Pal.Restore(last);
        Pal.Restore(pair);
        Pal.Restore(whole);
    }

    /// <summary>A read-only suffix, read and handed straight back.</summary>
    [Requires("0 <= p && p < Contents(v).Length")]
    [Ensures("Contents(v).Length == Old(Contents(v)).Length")]
    [Ensures("Contents(v).Length > p && p >= 0 && Result == Contents(v)[p]")]
    public static int PeekAt(int[] v, int p)
    {
        ReadOnlySpan<int> tail = v.AsSpan(p);
        int got = Peek(tail, 0);
        Pal.Restore(tail);
        return got;
    }

    /// <summary>Two-argument `AsSpan` where the original reached the same cell by a range.</summary>
    [Requires("3 <= Contents(v).Length")]
    [Ensures("Contents(v).Length == Old(Contents(v)).Length")]
    [Ensures("Contents(v).Length > 2 && Contents(v)[2] == 9")]
    public static void PokeThird(int[] v)
    {
        Span<int> mid = v.AsSpan(2, 1);
        mid[0] = 9;
        Pal.Restore(mid);
    }
}
