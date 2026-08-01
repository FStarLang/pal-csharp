using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Variant of <see cref="Summing"/> (plan §7.2): the counted `for` becomes a `while`
/// with the increment written before the accumulation rather than after, the
/// accumulator is updated by an explicit assignment rather than `+=`, and the
/// measure is given by hand rather than inferred. Same contract, same proof.
/// </summary>
public static class SummingVariant
{
    [Requires("SumsFit(Contents(a))")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    [Ensures("Result == SumUpTo(Contents(a), a.Length)")]
    public static int Sum(int[] a)
    {
        int running = 0;
        int seen = 0;
        while (seen < a.Length)
        {
            Pal.Invariant(Summing.SumsFit(Pal.Contents(a)));
            Pal.Invariant(0 <= seen && seen <= Pal.Contents(a).Length);
            Pal.Invariant(running == Summing.SumUpTo(Pal.Contents(a), seen));
            Pal.Decreases(int.MaxValue - seen);

            Summing.SumUpToStep(Pal.Contents(a), seen);
            running = running + a[seen];
            seen = seen + 1;
        }
        return running;
    }
}
