// EXPECT: PALCS0527
// A fact about the model alone does not belong in the invariant (R3.9d, F17).
//
// `[Invariant("Balance() >= 0")]` reads: the balance is never negative. It is true, it
// is provable, and the generated class module verifies -- which is precisely the trap.
// The invariant is opaque to a caller, so a client holding `class_Account__inv a m` can
// deduce nothing from a conjunct buried inside it; the fact reaches no one, and the
// failure shows up in a *different* file, as an unprovable client postcondition, with
// nothing to point at.
//
// The fix is placement, not strength: written as `[Refine("Result >= 0")]` on the
// [Model] member the same fact becomes part of the model *type*, so it travels with
// every model value the caller ever holds. F17 pins both halves of this experimentally.
//
// `[Invariant("cents >= 0")]` -- the same fact about the *field* -- is the legitimate
// clause, and is what makes the refinement provable when the invariant is re-folded.
using PalLang;

[Invariant("Balance >= 0")]
public sealed class ModelFactInInvariant
{
    private int cents;

    [Model]
    private SpecInt Balance => cents;

    [Ensures("Result >= 0")]
    public int Read() => cents;
}
