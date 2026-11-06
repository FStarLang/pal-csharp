// EXPECT: PALCS0704
// R27.12. A computed property's contract is written on the property or on its `get`
// accessor, not on both.
using PalLang;

public class Box
{
    private int value;

    [Model] private SpecInt Model => value;

    [Ensures("Result >= 0")]
    public int Value
    {
        [Ensures("Result == @this.Model")]
        get => value;
    }
}
