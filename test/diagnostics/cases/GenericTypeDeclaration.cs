// EXPECT: PALCS0581
// R15.1. M9 translates a generic class that stands alone. A generic struct is not that
// case: a struct is a *value* here -- copied at every assignment, stored inline in
// whatever holds it -- so its representation is §8's record rather than a reference with
// an invariant, and parameterising a record is a different problem from parameterising a
// class. Refused rather than translated by analogy.
using PalLang;

public struct Boxed<T>
{
    public T Item;
    public int Count;
}
