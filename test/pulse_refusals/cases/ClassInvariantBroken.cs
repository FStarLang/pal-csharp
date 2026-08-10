// EXPECT-PULSE: class_ClassInvariantBroken__model__pred
// R4.10. A class invariant is a proof obligation at every point where the object is handed
// back: the method may break it in the middle, and must have restored it by the end. This
// one does not restore it. `Withdraw` subtracts without checking, so a balance the
// invariant says is non-negative can be left negative.
using PalLang;

[Invariant("balance >= 0")]
public sealed class ClassInvariantBroken
{
    private int balance;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Bal => balance;

    [Spec]
    public SpecInt TheBalance => Bal;

    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public ClassInvariantBroken(int b) { balance = b; }

    [Requires("amount >= 0")]
    // MARKER
    public void Withdraw(int amount)
    {
        balance = balance - amount;
    }
}
