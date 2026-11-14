// EXPECT: PALCS0715
// A successful declaration pattern must not hide an exact subclass behind its base.
using PalLang;

public class PatternGauge
{
    private int level;
    [Model] private SpecInt Model => level;
    [Spec] public SpecInt Level => Model;
    [Ensures("Result == @this.Level")]
    public virtual int Read() => level;
}

public sealed class PatternFixedGauge : PatternGauge
{
    [Ensures("Result == @this.Level")]
    public override int Read() => base.Read();

    [Ensures("Result == @this.Level")]
    public int Widen()
    {
        if (this is PatternGauge wider) return wider.Read();
        else return 0;
    }

    public static class PatternGaugeUse
    {
        public static int Read()
        {
            PatternFixedGauge gauge = new PatternFixedGauge();
            return gauge.Widen();
        }
    }
}
