using PalLang;

/// <summary>
/// R9.21. An <em>open concrete</em> class: ordinary C#, with fields, a constructor, a
/// non-virtual method with a body and virtual methods with bodies — and not
/// <c>sealed</c>, so anyone may derive from it.
///
/// <para>Every other hierarchy test in this suite is written in the shape §9 translates
/// directly: an <c>abstract</c> root and <c>sealed</c> leaves. This one is written the way
/// a C# programmer writes a class, and R9.21's desugaring is what puts it into that
/// shape — an abstract half <c>Account</c> carrying the contracts, and a generated leaf
/// <c>Account__impl</c> carrying the representation and the bodies.</para>
///
/// <para>The consequence to look for is on <c>Fee</c>. R9.7 puts a <c>virtual</c> method's
/// contract on the abstract half, so a caller learns only what that contract says even
/// when it can see the <c>new</c> — which is exactly what C# itself gives a caller of an
/// overridable method. A <em>non-virtual</em> method keeps its contract exactly, which is
/// why <c>Bank.Basic</c> can prove an equality.</para>
/// </summary>
[Invariant("balance >= 0")]
public class Account
{
    protected int balance;

    /// <summary>
    /// R9.21b. The abstraction function of an open class is a <em>concrete</em> member —
    /// C# offers no way to make it abstract on a class that is also instantiable. So a
    /// subclass cannot override it, its model is inherited whole, and R9.6's forgetting
    /// function is the identity.
    /// </summary>
    [Refine("Result >= 0")]
    [Model]
    protected SpecInt Bal => balance;

    [Spec]
    public SpecInt TheBalance => Bal;

    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public Account(int b) { balance = b; }

    /// <summary>Not virtual, so its contract is exact at every call site.</summary>
    [Requires("amt >= 0")]
    [Requires("@this.TheBalance + amt <= 2147483647")]
    [Ensures("@this.TheBalance == Old(@this.TheBalance) + amt")]
    public void Deposit(int amt) { balance = balance + amt; }

    [Frac("p")]
    [Requires("@this.TheBalance <= 2147483647")]
    [Ensures("Result == @this.TheBalance")]
    public virtual int Get() { return balance; }

    /// <summary>
    /// Overridable, so the contract has to hold of every override there could ever be —
    /// including ones in another assembly. It says a range, not a value.
    /// </summary>
    [Frac("p")]
    [Ensures("0 <= Result && Result <= 100")]
    public virtual int Fee() { return 0; }
}
