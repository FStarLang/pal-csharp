using PalLang;

/// <summary>
/// R9.21b. An ordinary subclass of an open concrete class. It inherits the
/// representation, the invariant and the model, keeps <c>Deposit</c> and <c>Get</c>
/// without saying so, and overrides <c>Fee</c>.
///
/// <para>R9.21c. <c>: base(b)</c> chains to the base's constructor. There is one object
/// here, not two, so the base's constructor body is <em>inlined</em>: its parameters are
/// bound to the arguments and its field assignments run before this one's. R4.12c's
/// reading of <c>: this(args)</c> — that the chained constructor is the result — is
/// precisely what does not hold of <c>base</c>.</para>
/// </summary>
public class Premium : Account
{
    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    public Premium(int b) : base(b) { }

    public override int Fee() { return 5; }
}

/// <summary>
/// A third level, so flattening has to compose: <c>Gold</c> inherits <c>Account</c>'s
/// field through <c>Premium</c>, and inherits <c>Premium</c>'s replicated bodies rather
/// than <c>Account</c>'s originals. R9.21b runs base-first by depth for exactly this
/// reason.
/// </summary>
public class Gold : Premium
{
    [Requires("b >= 10")]
    [Ensures("@this.TheBalance == b")]
    public Gold(int b) : base(b) { }

    public override int Fee() { return 10; }

    /// <summary>A method the deepest class adds for itself, with an exact contract.</summary>
    [Frac("p")]
    [Requires("@this.TheBalance <= 2147483000")]
    [Ensures("Result == @this.TheBalance + 7")]
    public int Bonus() { return balance + 7; }
}
