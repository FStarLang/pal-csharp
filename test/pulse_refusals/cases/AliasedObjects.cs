// EXPECT-PULSE: class_Account__inv
// F16/R3.13. Ownership is exclusive, so `Transfer(a, a, 1)` asks for one account's
// invariant twice. Pulse holds one of them and says so.
//
// This used to be a frontend refusal (`PALCS0520`), on the reasoning that Pulse's message
// is worse than a message written for the occasion. That reasoning was wrong twice over.
// It put a rule about separation logic in a pass that does not do separation logic, where
// it could only ever be an approximation — it saw `f(a, a)` and nothing else, so it missed
// `f(a, a.Inner)` and every other way two arguments can name one resource. And an
// approximation in the frontend is worse than a precise answer in the verifier, because
// it is the frontend that has to be trusted.
//
// Removing it also uncovered a bug this file had been hiding: `Transfer` used to require
// `@from.Balance + amount <= int.MaxValue` while depositing into `to`, so the method did
// not verify on its own account. The check refused the file before it was ever emitted,
// so nobody found out. That is the general hazard with a frontend that answers questions
// the verifier should answer.
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
    [Requires("@to.Balance + amount <= 2147483647")]
    [Ensures("@to.Balance == Old(@to.Balance) + amount")]
    public static void Transfer(Account from, Account to, int amount)
    {
        to.Deposit(amount);
    }

    // One account, two owned parameters.
    public static void SelfTransfer(Account a)
    {
        // MARKER
        Transfer(a, a, 1);
    }
}
