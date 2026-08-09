using PalLang;

/// <summary>
/// R9.21d. An open concrete class whose <c>[Model]</c> member is <c>virtual</c>.
///
/// <para>R9.21b said a subclass of an open class inherits its model whole and R9.6's
/// forgetting function is the identity, because the <c>[Model]</c> member of an
/// instantiable class is <em>concrete</em> and C# will not let a subclass override a
/// non-virtual member. That was a statement about this one declaration, not about the
/// scheme: <c>virtual</c> is the C# for "a subclass may replace this", and once it is
/// written R9.6 applies exactly as it does to an abstract base. <c>Rewards</c> is the
/// evidence — its model carries a component <c>Acct</c>'s cannot name.</para>
///
/// <para>Nothing here is a new rule. The base declares its model and abstracts it from
/// its own field; a subclass that wants no more says nothing and gets R9.21b's identity;
/// a subclass that wants more declares a <c>[Model]</c> of its own and overrides this one
/// to say what an <c>Acct</c>'s model is in terms of it.</para>
/// </summary>
[Invariant("balance >= 0")]
public class Acct
{
    protected int balance;

    /// <summary>
    /// R9.5's abstraction function, and <c>virtual</c> so that R9.6 has somewhere to go.
    /// </summary>
    [Refine("Result >= 0")]
    [Model]
    protected virtual SpecInt Bal => balance;

    /// <summary>
    /// R3.9c. An observation, so a contract can name the model. It is written against
    /// <c>Bal</c>, which is why R9.21d does not copy it into a subclass that has a model
    /// of its own: there, <c>Bal</c> is the forgetting function and not the model.
    /// </summary>
    [Spec]
    public SpecInt TheBalance => Bal;

    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public Acct(int b) { balance = b; }

    [Frac("p")]
    [Requires("@this.TheBalance <= 2147483647")]
    [Ensures("Result == @this.TheBalance")]
    public virtual int Get() { return balance; }
}
