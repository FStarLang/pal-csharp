// EXPECT: PALCS0591
// R18.1. An indexer is a pair of accessors under the name `this[]`, which R2.1 cannot
// mangle into a module name and R9.5 has no field for. It was silently dropped.
using PalLang;

public sealed class Row
{
    private int a;

    [Model]
    private SpecInt TheA => a;

    public Row(int x)
    {
        this.a = x;
    }

    public int this[int i] => a;
}
