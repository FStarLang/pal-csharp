// EXPECT: PALCS0531
// R3.10b lifted the refusal on a field of *class* type: a class is a heap cell with
// identity, so its invariant can contain another object's the way R3.10a lets it contain
// an array's `A.pts_to`. What is still refused is a field whose type is spec-only. A `Seq`
// is a mathematical value with no runtime representation and no resource, so there is
// nothing for the invariant to hold and nothing for the constructor to allocate. Held in a
// class field it would look like storage while being nothing of the kind.
using PalLang;

public sealed class Log
{
    private Seq<int> entries;
    private int n;

    [Model]
    private SpecInt Model => n;

    [Spec]
    public SpecInt Count => Model;

    [Ensures("@this.Count == 0")]
    public Log()
    {
        n = 0;
    }
}
