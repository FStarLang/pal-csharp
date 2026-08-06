// EXPECT: PALCS0582
// R15.4. Legal C#, and not an F* inductive: the recursive occurrence is at `(T, T)` rather
// than at the declaring parameter, so the type it defines is non-uniform -- the family of
// types it generates is infinite. F* would need an inductive-inductive definition, which
// the scheme does not have, so the field is refused.
using PalLang;

public sealed class Nest<T>
{
    internal T item;
    internal Nest<(T, T)>? deeper;

    [Model]
    private SpecInt Contents => 0;
}
