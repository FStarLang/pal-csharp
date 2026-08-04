// EXPECT: PALCS0570
// R11.5. A `[SpecType]` denotes an F* type. It has no representation of its own: no
// fields to own, no invariant to hold, and no model to abstract it by — it *is* the
// model. Asking for a `[Model]` as well asks the translator to be two things at once,
// and there is no answer to which one a use of the type means.
using PalLang;

[SpecType("Doubled.bag")]
public sealed class DoubledBag
{
    [Model]
    private SpecList<SpecInt> Contents => SpecList.Empty<SpecInt>();
}
