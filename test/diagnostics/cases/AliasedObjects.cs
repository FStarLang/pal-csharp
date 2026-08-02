// EXPECT: PALCS0520
// R3.13/F16. Ownership is exclusive, so `Transfer(a, a, 1)` asks for one account's
// invariant twice and can never be proved. That is the correct outcome — the alternative
// would be unsound — but F* reports it as a bare `Cannot prove: class_Account__inv a _`
// against generated Pulse, which tells someone who wrote `Transfer(a, a, 1)` nothing at
// all. Refusing the call here changes no translation; it only puts the diagnosis on the
// line the mistake is on.
using PalLang;

[Invariant("balance >= 0")]
public sealed class Account
{
    private int balance;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Model => balance;

    [Spec]
    public SpecInt Balance => Model;

    [Requires("0 <= amount")]
    [Requires("@this.Balance + amount <= 2147483647")]
    [Ensures("@this.Balance == Old(@this.Balance) + amount")]
    public void Deposit(int amount)
    {
        balance = balance + amount;
    }
}

public static class Bank
{
    [Requires("0 <= amount")]
    [Requires("@from.Balance + amount <= 2147483647")]
    [Ensures("@to.Balance == Old(@to.Balance) + amount")]
    public static void Transfer(Account from, Account to, int amount)
    {
        to.Deposit(amount);
    }

    public static void SelfTransfer(Account a)
    {
        Transfer(a, a, 1);
    }
}
