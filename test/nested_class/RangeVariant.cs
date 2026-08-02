using PalLang;

namespace PalCSharp.Tests;

/// <summary>The same composite model, fields in the other order.</summary>
[Spec]
public struct SpanModel
{
    public CounterModel Top;
    public CounterModel Bottom;
}

/// <summary>
/// §7.2's variant detector for R3.10b. The same class as <c>Range</c>, written every other
/// way C# allows: members in the opposite order, both fields renamed, <c>this.</c> written
/// out, the composite model's two components declared the other way round, the invariant
/// stated as <c>!(a &gt; b)</c> rather than <c>a &lt;= b</c>, a <c>for</c> loop where
/// <c>Range</c> uses <c>while</c>, and expression bodies where <c>Range</c> uses blocks.
///
/// Modulo names the emitted Pulse is the same, and every remaining difference is one this
/// file *asked* for: the two sub-invariants and the two model components appear in the
/// order they are declared in, and <c>Width</c> reads its two counters in the order it
/// names them, because R6.2 preserves C#'s evaluation order. What matters is what does
/// <em>not</em> differ — <c>AdvanceBy</c>'s <c>for</c> loop carries exactly the resources
/// <c>Range</c>'s <c>while</c> loop carries, quantifies exactly the same sub-model, and
/// names the other one before the loop.
/// </summary>
[Invariant("!(bottom.N > top.N)")]
public sealed class Span
{
    [Ensures("Result == @this.Stop - @this.Start")]
    public int Width() => this.top.Value() - this.bottom.Value();

    [Requires("0 <= n")]
    [Requires("@this.Start + n <= @this.Stop")]
    [Ensures("@this.Start == Old(@this.Start) + n")]
    [Ensures("@this.Stop == Old(@this.Stop)")]
    public void AdvanceBy(int n)
    {
        for (int i = 0; i < n; i++)
        {
            Pal.Invariant(0 <= i && i <= n);
            Pal.Invariant(this.bottom.N == Pal.Old(this.Start) + i);
            Pal.Invariant(this.bottom.N + (n - i) <= this.top.N);
            Pal.Decreases(n - i);
            this.bottom.Bump();
        }
    }

    [Requires("@this.Start < @this.Stop")]
    [Ensures("@this.Start == Old(@this.Start) + 1")]
    [Ensures("@this.Stop == Old(@this.Stop)")]
    public void Advance() => this.bottom.Bump();

    [Requires("0 <= from && from <= to")]
    [Ensures("@this.Start == from")]
    [Ensures("@this.Stop == to")]
    public Span(int from, int to)
    {
        this.bottom = new Counter(from);
        this.top = new Counter(to);
    }

    [Spec]
    public SpecInt Stop => this.Model.Top.N;

    [Spec]
    public SpecInt Start => this.Model.Bottom.N;

    [Model]
    private SpanModel Model => new SpanModel
    {
        Top = this.top.State,
        Bottom = this.bottom.State,
    };

    private Counter top;
    private Counter bottom;
}
