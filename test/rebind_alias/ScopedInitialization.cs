using PalLang;

// Object cleanup must request an annotated tail independently of scalar storage.
public static class ScopedInitialization
{
    [Ensures("Result == 42")]
    public static int NoScalar(bool branch)
    {
        if (branch)
        {
            Counter local = new Counter();
            local.Get();
        }
        return 42;
    }

    [Requires("0 <= calls && calls < 100")]
    [Ensures("calls == Pal.Old(calls) + 1")]
    [Ensures("Result.Value == 0")]
    private static Counter Create(ref int calls)
    {
        calls++;
        return new Counter();
    }

    [Requires("0 <= calls && calls < 97")]
    [Ensures("calls == Pal.Old(calls) + (branch ? 3 : 2)")]
    [Ensures("Result == calls")]
    public static int EffectfulFactory(bool branch, ref int calls)
    {
        if (branch)
        {
            Counter local = Create(ref calls);
            int ignored = local.Get();
        }
        calls += 2;
        return calls;
    }
}
