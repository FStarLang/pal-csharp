using PalLang;

/// <summary>
/// Clients. R9.21's point is that these are written against <c>Account</c> and neither
/// know nor care that the class was split.
/// </summary>
public static class Bank
{
    /// <summary>
    /// A non-virtual method keeps its exact contract, so this proves an equality even
    /// though <c>Account</c> is open.
    /// </summary>
    [Ensures("Result == 30")]
    public static int Basic()
    {
        Account a = new Account(10);
        a.Deposit(20);
        return a.Get();
    }

    /// <summary>R9.21a. `new Premium(4)` really does yield an `Account`.</summary>
    [Ensures("Result == 44")]
    public static int PremiumBasic()
    {
        Account a = new Premium(4);
        a.Deposit(40);
        return a.Get();
    }

    /// <summary>Three levels, all reached through the root's type.</summary>
    [Ensures("Result == 66")]
    public static int GoldBasic()
    {
        Account a = new Gold(11);
        a.Deposit(55);
        return a.Get();
    }

    /// <summary>
    /// Dynamic dispatch over the whole chain. Each call is resolved through
    /// <c>Account</c>'s slot, so each learns only the abstract half's contract — which is
    /// why the sum is bounded rather than equal to 15.
    /// </summary>
    [Ensures("0 <= Result && Result <= 300")]
    public static int Fees()
    {
        Account x = new Account(0);
        Account y = new Premium(0);
        Account z = new Gold(10);
        return x.Fee() + y.Fee() + z.Fee();
    }

    /// <summary>A parameter of the open class's type, taken and given back (R4.10).</summary>
    [Requires("acct.TheBalance + 100 <= 2147483647")]
    [Ensures("Result == Old(acct.TheBalance) + 100")]
    public static int Fund(Account acct)
    {
        acct.Deposit(100);
        return acct.Get();
    }

    /// <summary>A method declared only at the deepest class, called at that type.</summary>
    [Ensures("Result == 27")]
    public static int GoldBonus()
    {
        Gold g = new Gold(20);
        return g.Bonus();
    }
}
