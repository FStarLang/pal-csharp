// EXPECT-PULSE: B.pts_to
// R4.11c through dispatch, and R9.21's hierarchy. The slot `FracSlot.Fee` is declared
// `[Frac]`, so every caller that dispatches through it is promised its receiver back
// unchanged. This override writes a field instead.
//
// The override carries no annotation of its own -- R9.7 forbids it -- so the only thing
// that says "read-only" here is the declaration it fills. Getting the answer from there
// rather than from the override's own body is what makes the emitted signature honest,
// and it is what lets Pulse refuse the write against the method the user wrote. Before
// that, the body's write set won locally and the annotation won at the vtable, and F*
// reported `Too many arguments` inside a generated vtable naming nothing in this file.
using PalLang;

[Invariant("balance >= 0")]
public class FracSlot
{
    protected int balance;

    [Refine("Result >= 0")]
    [Model]
    protected SpecInt Bal => balance;

    [Spec]
    public SpecInt TheBalance => Bal;

    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public FracSlot(int b) { balance = b; }

    [Frac("p")]
    [Ensures("0 <= Result && Result <= 100")]
    public virtual int Fee() { return 0; }
}

public class FracSlotSneaky : FracSlot
{
    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public FracSlotSneaky(int b) : base(b) { }

    public override int Fee()
    {
        // The write is a *store*, not an increment, so nothing here can overflow and the
        // invariant `balance >= 0` still holds afterwards. The only thing wrong with this
        // method is that it writes at all.
        // MARKER
        balance = 0;
        return 1;
    }
}
