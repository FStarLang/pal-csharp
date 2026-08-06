// EXPECT: PALCS0581
// R15.1. A generic class that participates in a hierarchy. §9's vtable is a record of
// function pointers whose types mention the class; parameterising the class parameterises
// the vtable, and the cast lemmas that relate a derived record to its base have to be
// parameterised alongside it. Neither is designed, so the declaration is refused rather
// than translated into a vtable whose type arguments do not line up.
using PalLang;

public abstract class Holder<T>
{
    internal T item;

    [Model]
    private SpecInt Contents => 0;
}
