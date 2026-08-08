// EXPECT: PALCS0598
// R4.12c. Chaining is the whole body or it is refused. `Func_Chained__ctor_int` returns the
// object with `class_Chained__inv` already folded, so the assignment after it needs the
// representation back -- and this constructor is not the one that closed the bracket.
// Choosing an unfold point here would be the emitter inventing R4.10c's fold from the
// other end.
using PalLang;

[Invariant("a <= b")]
public sealed class Chained
{
    private int a;
    private int b;

    [Model]
    private SpecInt Gap => b - a;

    [Spec]
    public SpecInt Width => Gap;

    [Requires("k <= 0")]
    [Ensures("@this.Width == 0 - k")]
    public Chained(int k)
    {
        this.a = k;
        this.b = 0;
    }

    [Ensures("@this.Width == 1")]
    public Chained() : this(0)
    {
        this.b = 1;
    }
}
