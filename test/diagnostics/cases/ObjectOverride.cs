// EXPECT: PALCS0591
// R18.1. An override of an `object` member is dispatch through a root the scheme does not
// model: R9.8 makes a reference a `dyn` witnessed at the class the program declares, and
// `System.Object` is not one of those. Emitting it named `Class_Object`, a module that is
// never generated — the defect R18.2's lint now detects.
using PalLang;

public sealed class Tag
{
    private int id;

    [Model]
    private SpecInt TheId => id;

    public Tag(int k)
    {
        this.id = k;
    }

    public override int GetHashCode()
    {
        return id;
    }
}
