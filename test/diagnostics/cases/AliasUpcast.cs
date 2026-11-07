// EXPECT: PALCS0715
// R27.57. An object of a representation-sharing subclass is verified at its exact class,
// so it may not be converted to its base: a call through the base would run the base's
// body where the subclass's override runs.
using PalLang;

public class Gauge
{
    private int level;

    [Model] private SpecInt Model => level;

    [Spec] public SpecInt Level => Model;

    [Ensures("Result == @this.Level")]
    public virtual int Read() => level;
}

public sealed class FixedGauge : Gauge
{
    [Ensures("Result == @this.Level")]
    public override int Read() => base.Read();
}

public static class GaugeUse
{
    public static int Widen()
    {
        FixedGauge g = new FixedGauge();
        Gauge b = g;
        return b.Read();
    }
}
