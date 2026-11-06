// EXPECT: PALCS0713
// R27.46. An argument at an `[Exactly(typeof(C))]` parameter must be a non-null `C`: an
// `object` could be anything.
using PalLang;

public sealed class Cell
{
    private int value;

    [Model] private SpecInt Model => value;

    [Ensures("true")]
    public Cell(int v)
    {
        value = v;
    }

    [Ensures("true")]
    public static int Read([Exactly(typeof(Cell))] object source) => 0;

    [Ensures("true")]
    public static int Pass(object o) => Read(o);
}
