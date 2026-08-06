// EXPECT: PALCS0580
// R14.1, restated at a type declaration. A constraint is a typeclass obligation, and the
// dictionary a use of it would need is not part of the scheme -- at a method (R14.1) and
// equally at the type that declares the parameter. This is why test/generic_tree orders
// its search tree by an `int` key rather than by `IComparable<T>`.
using PalLang;

public sealed class Sorted<T> where T : System.IComparable<T>
{
    internal T least;

    [Model]
    private SpecInt Contents => 0;
}
