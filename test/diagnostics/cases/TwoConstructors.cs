// EXPECT: PALCS0501
// R18.3. Both constructors mangle to the module `Func_Pair__ctor` (R2.1), so one would
// overwrite the other. Before this was reported the emitter built a dictionary keyed by
// module name and crashed on the duplicate — after emitting, so the diagnostic that would
// have explained it was never printed.
using PalLang;

public sealed class TwoCtors
{
    private int a;

    [Model]
    private SpecInt TheA => a;

    public TwoCtors()
    {
        this.a = 0;
    }

    public TwoCtors(int x)
    {
        this.a = x;
    }
}
