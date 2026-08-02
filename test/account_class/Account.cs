using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Two objects at once, and the property that needs them: conservation.
/// <c>test/counter_class</c> and <c>test/stack_class</c> each reason about a single
/// object, where separation is invisible because there is nothing to be separate from.
/// Here it is the whole content of the proof — <c>Transfer</c> concludes that the pair's
/// total is unchanged, and it may do so only because holding two invariants means holding
/// two <em>distinct</em> objects (F16).
/// </summary>
[Invariant("balance >= 0")]
public sealed class Account
{
    private int balance;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Model => balance;

    [Spec]
    public SpecInt Balance => Model;

    [Requires("0 <= initial")]
    [Ensures("@this.Balance == initial")]
    public Account(int initial)
    {
        balance = initial;
    }

    [Requires("0 <= amount")]
    [Requires("@this.Balance + amount <= 2147483647")]
    [Ensures("@this.Balance == Old(@this.Balance) + amount")]
    public void Deposit(int amount)
    {
        balance = balance + amount;
    }

    /// <summary>
    /// The precondition is what keeps <c>[Refine("Result &gt;= 0")]</c> provable at the
    /// re-fold. Drop it and the failure appears here, at the fold, rather than at some
    /// later caller who assumed a balance was non-negative — which is R3.9d's point about
    /// where each kind of fact belongs.
    /// </summary>
    [Requires("0 <= amount")]
    [Requires("amount <= @this.Balance")]
    [Ensures("@this.Balance == Old(@this.Balance) - amount")]
    public void Withdraw(int amount)
    {
        balance = balance - amount;
    }

    [Ensures("Result == @this.Balance")]
    public int Read()
    {
        return balance;
    }
}

public static class Bank
{
    /// <summary>
    /// Conservation. The first <c>[Ensures]</c> is the interesting one: it mentions both
    /// objects, so it can only be stated because each has its own model binder, and it can
    /// only be proved because the second call cannot have disturbed the first object.
    /// Neither fact is asserted anywhere — separation supplies both.
    ///
    /// <c>Transfer(a, a, 1)</c> is <b>PALCS0520</b>. It is not unsound, it is unprovable
    /// (R3.13): the call asks for one account's invariant twice.
    /// </summary>
    [Requires("0 <= amount")]
    [Requires("amount <= @from.Balance")]
    [Requires("@to.Balance + amount <= 2147483647")]
    [Ensures("@from.Balance == Old(@from.Balance) - amount")]
    [Ensures("@to.Balance == Old(@to.Balance) + amount")]
    [Ensures("@from.Balance + @to.Balance == Old(@from.Balance) + Old(@to.Balance)")]
    public static void Transfer(Account from, Account to, int amount)
    {
        from.Withdraw(amount);
        to.Deposit(amount);
    }

    /// <summary>
    /// A fresh pair. Freshness costs nothing to state: the frame rule hands each
    /// constructor `frame ** inv x m`, so the second account is automatically separate
    /// from the first, and both are dropped at the exit (R4.14).
    /// </summary>
    [Ensures("Result == 30")]
    public static int OpenAndTransfer()
    {
        Account a = new Account(100);
        Account b = new Account(0);
        Transfer(a, b, 30);
        return b.Read();
    }
}
