// EXPECT: PALCS0531
// R3.10a draws the line between the two resources a class field might hold. An array is
// allowed: the invariant gains one `A.pts_to`, and the contents are an existential every
// method threads. Another *object* is not, and the reason is not effort. Its invariant is
// already an abstraction with its own fold/unfold window, so nesting it would ask when the
// outer object may open the inner one — during its own window? across a call to the inner
// object's method? — and the scheme has no answer. Refusing it is the honest outcome
// until one is written down.
using PalLang;

public sealed class Cell
{
    private int v;

    [Model]
    private SpecInt Model => v;

    [Spec]
    public SpecInt Value => Model;

    [Ensures("@this.Value == 0")]
    public Cell()
    {
        v = 0;
    }
}

public sealed class Pair
{
    private Cell left;
    private int right;

    [Model]
    private SpecInt Model => right;

    [Spec]
    public SpecInt Right => Model;

    [Ensures("@this.Right == 0")]
    public Pair()
    {
        left = new Cell();
        right = 0;
    }
}
