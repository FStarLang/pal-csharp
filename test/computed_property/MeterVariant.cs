// §7.2's variant detector for R9.20. The same program with every computed property written
// as the ordinary method it is, and the two remaining ones swapped between the accessor
// forms. R9.20 says a computed property *is* the method its getter is; if that is true,
// this file needs no translator change, and the reader may check it by comparing
// `Func_Meter_Span` here with `Func_Gauge_Span` next door.
using PalLang;

namespace Instruments;

[Invariant("bottom <= top")]
[Invariant("top - bottom <= 2147483647")]
public sealed class Meter
{
    private int bottom;
    private int top;

    [Model]
    private Bounds Model => new Bounds { Lo = bottom, Hi = top };

    [Spec]
    public SpecInt Lo => Model.Lo;

    [Spec]
    public SpecInt Hi => Model.Hi;

    [Requires("lo <= hi")]
    [Requires("hi - lo <= 2147483647")]
    [Ensures("@this.Lo == lo")]
    [Ensures("@this.Hi == hi")]
    public Meter(int lo, int hi)
    {
        this.bottom = lo;
        this.top = hi;
    }

    /// <summary>Written as a method where `Gauge` wrote an expression-bodied property.</summary>
    [Ensures("Result == @this.Hi - @this.Lo")]
    public int Span()
    {
        return top - bottom;
    }

    /// <summary>Written as an expression-bodied property where `Gauge` used a block.</summary>
    [Ensures("Result == @this.Lo + @this.Hi")]
    [Requires("-2147483648 <= @this.Lo + @this.Hi && @this.Lo + @this.Hi <= 2147483647")]
    public int Total => bottom + top;

    /// <summary>Written as a property where `Gauge` wrote a method, and the other way round.</summary>
    [Ensures("Result == @this.Hi - @this.Lo")]
    public int Width => Span();

    [Ensures("k < 0 || Result == 1")]
    [Ensures("k >= 0 || Result == 0")]
    public int AtLeast(int k)
    {
        if (k >= 0)
        {
            int unused = Span();
            return 1;
        }
        return 0;
    }
}

public static class Client
{
    [Ensures("Result == @g.Hi - @g.Lo")]
    public static int Read(Meter g)
    {
        return g.Width;
    }

    [Requires("@g.Lo <= @g.Hi")]
    [Requires("2 * (@g.Hi - @g.Lo) <= 2147483647")]
    [Ensures("Result == 2 * (@g.Hi - @g.Lo)")]
    public static int Twice(Meter g)
    {
        int a = g.Span();
        int b = g.Width;
        return a + b;
    }
}
