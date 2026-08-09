using PalLang;

/// <summary>
/// Clients. The pair of methods below is the claim R9.21d makes, stated twice: at the
/// subclass's own type the extended model is exact, and through a base-typed reference it
/// is forgotten down to the base's.
/// </summary>
public static class Bank
{
    /// <summary>The extra component is exact at the type that declares it.</summary>
    [Ensures("Result == 3")]
    public static int Points()
    {
        Rewards r = new Rewards(5);
        r.Award(3);
        return r.GetPoints();
    }

    /// <summary>
    /// R9.6. Converting to <c>Acct</c> applies the forgetting function, so what survives
    /// is the balance alone — unchanged by <c>Award</c>, which is exactly what
    /// <c>Award</c>'s second postcondition had to say for this to be provable.
    /// </summary>
    [Ensures("Result == 5")]
    public static int Balance()
    {
        Rewards r = new Rewards(5);
        r.Award(3);
        Acct a = r;
        return a.Get();
    }

    /// <summary>A plain <c>Acct</c> still works; R9.21b's identity case is untouched.</summary>
    [Ensures("Result == 7")]
    public static int Plain()
    {
        Acct a = new Acct(7);
        return a.Get();
    }
}
