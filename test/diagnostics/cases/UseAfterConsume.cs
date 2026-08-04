// EXPECT: PALCS0550
// R4.9c and R4.12b. A parameter the callee consumes takes the argument's invariant with it,
// so the caller no longer owns what it handed over. C# would let the name be read again —
// the reference is still there — but there is nothing left to read it out of, and saying so
// against the second use is more useful than an unprovable resource in generated Pulse.
using PalLang;

[Spec]
public struct TallyModel
{
    public SpecInt N;
}

[Invariant("0 <= k")]
public sealed class Tally
{
    private int k;

    [Refine("0 <= Result.N && Result.N <= 2147483647")]
    [Model]
    private TallyModel Model => new TallyModel { N = k };

    [Spec]
    public SpecInt N => Model.N;

    [Spec]
    public TallyModel State => Model;

    [Requires("0 <= start")]
    public Tally(int start)
    {
        k = start;
    }

    [Requires("@this.N < 2147483647")]
    [Ensures("@this.N == Old(@this.N) + 1")]
    public void Bump()
    {
        k = k + 1;
    }
}

[Invariant("0 <= held.N")]
public sealed class Keeper
{
    private Tally held;

    [Model]
    private TallyModel Model => held.State;

    [Spec]
    public SpecInt N => Model.N;

    public Keeper(Tally given)
    {
        held = given;
    }
}

public static class Keeping
{
    public static void Twice()
    {
        Tally t = new Tally(0);
        Keeper first = new Keeper(t);
        Keeper second = new Keeper(t);
    }
}
