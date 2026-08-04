// EXPECT: PALCS0573
// R11.2. This is the rule that makes the extension mechanism total. Every member of a
// specification type that a specification names must say what it means in F*; the
// translator will not guess an F* name from a C# one, because a wrong guess would be a
// silently mistranslated specification rather than an error.
//
// `Width` below is an ordinary C# property on a specification type. It has no
// `[SpecOp]`, so there is nothing to emit for it.
using PalLang;

[SpecType("Unnamed.gauge")]
public sealed class Gauge
{
    [SpecOp("Unnamed.height")]
    public SpecInt Height => throw new System.InvalidOperationException();

    public SpecInt Width => throw new System.InvalidOperationException();
}

public static class GaugeUse
{
    [Requires("g.Width > 0")]
    [Ensures("Result == 1")]
    public static int Check(Ghost<Gauge> g) => 1;
}
