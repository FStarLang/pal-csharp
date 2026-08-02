// EXPECT-PULSE: class_Counter__inv
// R3.10b. A sub-object is built by its owner. Storing one that was handed in instead —
// `this.inner = given` — asks for the argument's invariant twice: once to hand to the
// `fold` that establishes the owner's invariant, and once to give back, because a
// parameter that is not consumed is preserved.
//
// Whether that *should* be expressible is a design question (it wants a way to say a
// parameter is consumed, which the surface syntax has no word for yet). What it must not
// be is a frontend refusal guessing at the answer: the frontend cannot see that the
// argument is needed twice, only Pulse can, and Pulse says so exactly.
using PalLang;

[Spec]
public struct CounterModel
{
    public SpecInt N;
}

[Invariant("0 <= k")]
public sealed class Counter
{
    private int k;

    [Refine("0 <= Result.N && Result.N <= 2147483647")]
    [Model]
    private CounterModel Model => new CounterModel { N = k };

    [Spec]
    public SpecInt N => Model.N;

    [Spec]
    public CounterModel State => Model;

    [Requires("0 <= start")]
    public Counter(int start)
    {
        k = start;
    }
}

[Spec]
public struct BoxModel
{
    public CounterModel Inner;
}

[Invariant("0 <= inner.N")]
public sealed class Box
{
    private Counter inner;

    [Model]
    private BoxModel Model => new BoxModel { Inner = inner.State };

    // The parameter is preserved, and the `fold` also wants it.
    //
    // The message lands on the constructor, not on the assignment, and that is the right
    // answer rather than a rounding of it: the assignment is fine, and what cannot be
    // discharged is the constructor's *exit*, where it owes `this`'s invariant and
    // `given`'s back at once.
    // MARKER
    public Box(Counter given)
    {
        inner = given;
    }
}
