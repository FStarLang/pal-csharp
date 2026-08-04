// EXPECT: PALCS0560
// R10.5. A recursive class's invariant is the inversion of its `[Model]` equation, so the
// model has to be a type whose empty constructor is what a null reference denotes. A
// scalar has no empty constructor and no induction to invert, so there is nothing for the
// null case of the invariant to be — and guessing one would be inventing a proof step.
using PalLang;

public sealed class ScalarChain
{
    internal int value;
    internal ScalarChain? next;

    [Model]
    private SpecInt Total => value + next!.Sum;

    [Spec]
    public SpecInt Sum => Total;
}
