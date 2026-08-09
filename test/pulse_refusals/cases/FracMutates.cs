// EXPECT-PULSE: B.pts_to
// R4.11c. `[Frac("p")]` says the caller keeps a share and is handed the object back at the
// model it arrived at. This body assigns a field, so it needs full ownership. Whether a
// write is permitted at a fraction is a separation-logic question, and Pulse answers it:
// the assignment cannot be proved against `B.pts_to var_this #p _`.
//
// This was briefly a frontend refusal (`PALCS0551`), on the reasoning that the write set
// is visible in the source so the contradiction could be caught early. Same mistake as
// `AliasedObjects`, and the harness header above already said why: the frontend cannot see
// the prover's context, so its answer is an approximation, and an approximation in the
// frontend is worse than a precise answer in the verifier.
//
// The *real* defect underneath was not a missing check. `[Frac]` on a method (R9.7) is a
// second way to say "read-only", and `MethodPlan` re-derived a first one from the body;
// where they disagreed the body's answer silently won for the emitted signature and the
// annotation's won for the class-level declaration and the vtable slot. So a single class
// ignored the annotation outright, and a hierarchy emitted a *false* postcondition --
// `TheBalance == TheBalance + 7` -- into the slot every caller dispatches through. One
// answer about the receiver, and F* to judge it, is the fix. This file is the evidence
// that F* does judge it.
using PalLang;

[Invariant("balance >= 0")]
public sealed class FracMutates
{
    private int balance;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Bal => balance;

    [Spec]
    public SpecInt TheBalance => Bal;

    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public FracMutates(int b) { balance = b; }

    [Frac("p")]
    [Requires("@this.TheBalance + 7 <= 2147483647")]
    [Ensures("@this.TheBalance == Old(@this.TheBalance) + 7")]
    public int Bonus()
    {
        // MARKER
        balance = balance + 7;
        return balance;
    }
}
