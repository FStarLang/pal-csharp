// EXPECT: PALCS0597
// R4.10c. `Sum` reads `n` and also calls `Get()` on the same object. The field access
// needs the invariant unfolded and the call needs it folded, and one bracket cannot be
// both. It used to be emitted anyway — `unfold` followed by a call whose contract asks for
// the folded form — which is ill-typed Pulse produced with `0 error(s)`.
using PalLang;

public sealed class Doubler
{
    private int n;

    [Model]
    private SpecInt TheN => n;

    [Spec]
    public SpecInt N => TheN;

    public Doubler(int a)
    {
        this.n = a;
    }

    [Ensures("Result == @this.N")]
    public int Get()
    {
        return n;
    }

    [Requires("-1073741824 <= @this.N && @this.N <= 1073741823")]
    [Ensures("Result == 2 * @this.N")]
    public int Sum()
    {
        int x = n;
        int y = Get();
        return x + y;
    }
}
