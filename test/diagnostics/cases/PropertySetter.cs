// EXPECT: PALCS0591
// R9.20b. A computed property's getter is the method it is, but a setter's parameter is
// named `value` by C# rather than by the author, and §4 has no reading of that name in a
// specification — so a setter has no contract that can be written down.
using PalLang;

public sealed class Slot
{
    private int v;

    [Model]
    private SpecInt TheV => v;

    public Slot(int a)
    {
        this.v = a;
    }

    public int Value
    {
        get { return v; }
        set { v = value; }
    }
}
