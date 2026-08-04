using PalLang;

namespace PalCSharp.Tests;

/// <summary>A composite model: two sub-models, not two scalars.</summary>
[Spec]
public struct RangeModel
{
    public CounterModel Low;
    public CounterModel High;
}

/// <summary>
/// R3.10b. An object owning two objects, with an invariant that <em>relates</em> them.
/// `low.N &lt;= high.N` is a fact neither `Counter` could state — it is exactly the fact
/// that composition exists to express, and it is what makes `Advance`'s precondition
/// necessary.
/// </summary>
[Invariant("low.N <= high.N")]
public sealed class Range
{
    private Counter low;
    private Counter high;

    [Model]
    private RangeModel Model => new RangeModel { Low = low.State, High = high.State };

    [Spec]
    public SpecInt Start => Model.Low.N;

    [Spec]
    public SpecInt Stop => Model.High.N;

    [Requires("0 <= from && from <= to")]
    [Ensures("@this.Start == from")]
    [Ensures("@this.Stop == to")]
    public Range(int from, int to)
    {
        low = new Counter(from);
        high = new Counter(to);
    }

    /// <summary>
    /// A mutator that reaches into a sub-object. Inside R4.10's window the sub-object is
    /// still <em>folded</em> — the outer invariant contains the inner one rather than
    /// restating it — so this is an ordinary call, and the precondition it needs is the
    /// conjoined invariant's.
    /// </summary>
    [Requires("@this.Start < @this.Stop")]
    [Ensures("@this.Start == Old(@this.Start) + 1")]
    [Ensures("@this.Stop == Old(@this.Stop)")]
    public void Advance()
    {
        low.Bump();
    }

    /// <summary>
    /// R5.12 meets R3.10b. Inside the loop the sub-objects are carried the way an array's
    /// contents are: <c>low</c> is written, so its model is existentially quantified;
    /// <c>high</c> is only read through a method R4.11 found read-only, so its model is
    /// <em>named before the loop</em> and the invariant may say it did not move.
    /// </summary>
    [Requires("0 <= n")]
    [Requires("@this.Start + n <= @this.Stop")]
    [Ensures("@this.Start == Old(@this.Start) + n")]
    [Ensures("@this.Stop == Old(@this.Stop)")]
    public void AdvanceBy(int n)
    {
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i && i <= n);
            Pal.Invariant(low.N == Pal.Old(this.Start) + i);
            Pal.Invariant(low.N + (n - i) <= high.N);
            Pal.Decreases(n - i);
            low.Bump();
            i = i + 1;
        }
    }

    [Ensures("Result == @this.Stop - @this.Start")]
    public int Width()
    {
        int a = low.Value();
        int b = high.Value();
        return b - a;
    }
}

/// <summary>
/// R4.12b. An owner that does not build its sub-object but is <em>handed</em> one. A
/// constructor body may only initialise fields, so an object parameter it stores is
/// necessarily given away: the argument's invariant leaves the caller and becomes part of
/// the new object's. So a constructor consumes every object parameter, and no annotation
/// says so — the rule reads it off the shape of a constructor.
/// </summary>
[Invariant("0 <= inner.N")]
public sealed class Held
{
    private Counter inner;

    [Model]
    private CounterModel Model => inner.State;

    [Spec]
    public SpecInt N => Model.N;

    [Ensures("@this.N == Old(given.N)")]
    public Held(Counter given)
    {
        inner = given;
    }

    [Requires("@this.N < 2147483647")]
    [Ensures("@this.N == Old(@this.N) + 1")]
    public void Bump()
    {
        inner.Bump();
    }

    [Ensures("Result == @this.N")]
    public int Inspect()
    {
        return inner.Value();
    }
}
