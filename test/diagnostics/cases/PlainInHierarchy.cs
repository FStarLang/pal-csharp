// EXPECT: PALCS0575
// R12.1. A `[Plain]` class is a bare record behind a box: no vtable, no invariant, nothing
// for a base class's encoding to compose with. Subclassing one has no meaning in the
// translation, so it is refused rather than silently given one.
using PalLang;

public abstract class PlainBaseShape
{
}

[Plain]
public sealed class PlainDerivedShape : PlainBaseShape
{
    internal int side;
}
