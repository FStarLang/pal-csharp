// EXPECT: PALCS0627
// A generic exact receiver's runtime instantiation can make this test succeed.
using PalLang;

public sealed class ExactGenericCell<T>
{
    private int value;
    [Model] private SpecInt Model => value;
    [Ensures("true")]
    public bool IsInt() => this is ExactGenericCell<int>;
}
