// EXPECT-PULSE: class_Counter__inv
// R3.10. Inside an instance method the object's invariant is *unfolded* — that is what
// makes the fields readable. A call to another instance method on `this` needs it folded,
// because that is what the callee's contract asks for, and it is not there.
//
// This is by design, and it is deliberately not a frontend refusal. The frontend has no
// idea what is in the prover's context; Pulse does. The message names the resource that
// could not be produced, which is the true statement about why the call cannot be made.
using PalLang;

[Invariant("count >= 0")]
public sealed class Counter
{
    private int count;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Model => count;

    [Spec]
    public SpecInt Count => Model;

    [Requires("@this.Count < 2147483647")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    public void Increment()
    {
        count = count + 1;
    }

    // `Increment` wants `class_Counter__inv this _`. Here the invariant is open, so the
    // fields are visible and the folded resource is not.
    [Requires("@this.Count < 2147483646")]
    public void IncrementTwice()
    {
        // MARKER
        Increment();
        Increment();
    }
}
