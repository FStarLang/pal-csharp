// EXPECT: PALCS0594
// R18.1. An interface is not a `BaseType` in Roslyn, so the R9.1 walk over the base list
// never saw it: the class verified as though the interface were not there, and any
// contract stated on the interface member was simply absent.
using PalLang;

public interface ICount
{
    int Get();
}

public sealed class Ctr : ICount
{
    private int n;

    [Model]
    private SpecInt TheN => n;

    public Ctr(int k)
    {
        this.n = k;
    }

    public int Get()
    {
        return n;
    }
}
