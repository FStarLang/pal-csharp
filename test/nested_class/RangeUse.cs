using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R3.10b from the outside. A client of `Range` never names `low`, `high`, or `k` — it
/// sees two levels of abstraction collapsed into one model — and separation gives it the
/// facts about two composites that no single object could state.
/// </summary>
public static class RangeUse
{
    /// <summary>
    /// R4.12b from the outside. The caller builds a `Counter`, gives it away, and does not
    /// mention it again — which is the only thing it could do, because the constructor took
    /// its invariant with it.
    /// </summary>
    [Ensures("Result == 6")]
    public static int HandOver()
    {
        Counter c = new Counter(5);
        Held h = new Held(c);
        h.Bump();
        return h.Inspect();
    }

    /// <summary>The composite's model is what a client reasons about.</summary>
    [Ensures("Result == 3")]
    public static int BuildAndMeasure()
    {
        Range r = new Range(4, 7);
        return r.Width();
    }

    /// <summary>
    /// A read through a sub-object has to reach the caller. `Width` assigns nothing and
    /// calls only methods that assign nothing, so R4.11 gives it `preserves` and this
    /// caller still knows the range it measured is the range it started with.
    /// </summary>
    [Requires("r.Start < r.Stop")]
    [Ensures("Result == Old(r.Stop) - Old(r.Start)")]
    [Ensures("r.Start == Old(r.Start)")]
    public static int MeasureTwice(Range r)
    {
        int first = r.Width();
        int second = r.Width();
        return second;
    }

    /// <summary>
    /// Two composites are distinct, and advancing one leaves the other alone. Neither fact
    /// is stated anywhere: separation supplies both, and it supplies them through *two*
    /// levels of ownership — the `Counter`s inside `a` are as disjoint from those inside
    /// `b` as the `Range`s are.
    /// </summary>
    [Requires("a.Start < a.Stop")]
    [Ensures("a.Start == Old(a.Start) + 1")]
    [Ensures("b.Start == Old(b.Start)")]
    [Ensures("b.Stop == Old(b.Stop)")]
    public static void AdvanceOne(Range a, Range b)
    {
        a.Advance();
    }
}
