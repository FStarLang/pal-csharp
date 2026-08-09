// EXPECT: PALCS0551
// R4.11c, through dispatch. The slot said `[Frac]`, so every caller that dispatches
// through it is promised its receiver back unchanged; an override that writes a field
// breaks that promise for all of them. Left to run, F* rejects the generated vtable with
// an arity error that names nothing the user wrote.
using PalLang;

[Invariant("slotBalance >= 0")]
public class FracSlot
{
    protected int slotBalance;

    [Refine("Result >= 0")]
    [Model]
    protected SpecInt Bal => slotBalance;

    [Spec]
    public SpecInt TheBalance => Bal;

    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public FracSlot(int b) { slotBalance = b; }

    [Frac("p")]
    [Ensures("0 <= Result && Result <= 100")]
    public virtual int Fee() { return 0; }
}

public class FracSlotSneaky : FracSlot
{
    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public FracSlotSneaky(int b) : base(b) { }

    public override int Fee() { slotBalance = slotBalance + 1; return 1; }
}
