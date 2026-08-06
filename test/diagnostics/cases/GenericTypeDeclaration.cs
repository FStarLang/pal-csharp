// EXPECT: PALCS0581
// R14.1. M8 translates generic *methods*, not generic types. The record itself is
// representable — a parameterised `noeq type` is ordinary F* — but a type's invariant and
// its ownership predicate are what give a struct or class meaning here, and neither has
// been designed for a type parameterised by a type. So the declaration is refused, with
// the polymorphism to be kept in the methods instead.
using PalLang;

public struct Boxed<T>
{
    public T Item;
    public int Count;
}
