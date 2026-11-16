using System;
using PalLang;

namespace PalCSharp.Tests;

public static class TallySpec
{
    /// <summary>Every cell is zero.</summary>
    [Spec]
    public static bool AllZero(Seq<int> s) =>
        Pal.Forall((int k) => Pal.Implies(0 <= k && k < s.Length, s[k] == 0));

    /// <summary>`s` is `t` but at `i`. Named, as a lambda cannot mention a span (R17.6a).</summary>
    [Spec]
    public static bool SameBut(Seq<int> s, Seq<int> t, int i) =>
        Pal.Forall((int k) => Pal.Implies(0 <= k && k < s.Length && k < t.Length && k != i, s[k] == t[k]));
}

/// <summary>
/// R17.10. A `ref struct` over one span is that span: its members are functions of the
/// span, `_cells` and `Cells` name it, and its constructor runs over the span it is given.
/// </summary>
internal ref struct Tally
{
    private readonly Span<int> _cells;

    internal Span<int> Cells => _cells;

    /// <summary>R17.11: `Clear` zeroes the span.</summary>
    [Ensures("Pal.Contents(cells).Length == Pal.Old(Pal.Contents(cells)).Length")]
    [Ensures("Pal.Implies(wipe, TallySpec.AllZero(Pal.Contents(cells)))")]
    [Ensures("Pal.Implies(!wipe, Pal.Contents(cells) == Pal.Old(Pal.Contents(cells)))")]
    internal Tally(Span<int> cells, bool wipe)
    {
        if (wipe)
        {
            cells.Clear();
        }
        _cells = cells;
    }

    /// <summary>A writable alias of the field: the writes are the wrapper's.</summary>
    [Requires("0 <= i && i < Pal.Contents(@this.Cells).Length")]
    [Ensures("Pal.Contents(@this.Cells).Length == Pal.Old(Pal.Contents(@this.Cells)).Length")]
    [Ensures("Pal.Contents(@this.Cells)[i] == 1")]
    [Ensures("TallySpec.SameBut(Pal.Contents(@this.Cells), Pal.Old(Pal.Contents(@this.Cells)), i)")]
    internal void Stamp(int i)
    {
        Span<int> cells = _cells;
        cells[i] = 1;
    }

    /// <summary>A read-only alias of the field.</summary>
    [Requires("0 <= i && i < Pal.Contents(@this.Cells).Length")]
    [Ensures("Pal.Contents(@this.Cells) == Pal.Old(Pal.Contents(@this.Cells))")]
    [Ensures("Result == Pal.Contents(@this.Cells)[i]")]
    internal int At(int i)
    {
        ReadOnlySpan<int> cells = _cells;
        return cells[i];
    }
}

public static class SpanStructs
{
    /// <summary>
    /// R17.9 and R17.10: a `stackalloc`ed buffer, a window of it or a fresh array, chosen by
    /// a conditional, wrapped. Each arm has one origin; each `return` releases the spans.
    /// </summary>
    [Requires("2 <= n && n <= 100")]
    [Ensures("Result == 1")]
    public static int TallyFirst(int n)
    {
        Span<int> buffer = stackalloc int[8];
        Tally t = n <= 8 ?
            new Tally(buffer.Slice(0, n), wipe: true) :
            new Tally(new int[n], wipe: false);
        t.Stamp(0);
        if (t.At(1) == 0)
        {
            return t.At(0);
        }
        return 0;
    }
}
