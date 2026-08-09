using PalLang;

/// <summary>
/// R9.21d. A subclass whose model carries <em>strictly more</em> than its base's. An
/// <c>Acct</c> is known by its balance; a <c>Rewards</c> is known by its balance and its
/// points, and no function of an <c>Acct</c>'s model can recover the points.
///
/// <para>The two members are R9.5's and R9.6's, and they read different things (R9.6a):
/// <c>Full</c> abstracts the fields, and the <c>override</c> of <c>Bal</c> says what an
/// <c>Acct</c>'s model is in terms of <c>Full</c>. That the forgetting is a projection
/// rather than the identity is the whole point — it is what makes <c>Rewards</c> a proper
/// refinement of <c>Acct</c> rather than a renaming of it.</para>
/// </summary>
[Invariant("points >= 0")]
public class Rewards : Acct
{
    private int points;

    /// <summary>R9.5, over both fields — the inherited one and this class's own.</summary>
    [Refine("Result.Bal >= 0 && Result.Pts >= 0")]
    [Model]
    private SpecAcct Full => SpecAcctOps.Mk(balance, points);

    /// <summary>R9.6, a projection: an <c>Acct</c>'s model is the balance component.</summary>
    protected override SpecInt Bal => Full.Bal;

    /// <summary>An observation of what only <em>this</em> class's model can say.</summary>
    [Spec]
    public SpecInt ThePoints => Full.Pts;

    [Requires("b >= 0")]
    [Ensures("@this.TheBalance == b")]
    [Ensures("@this.ThePoints == 0")]
    public Rewards(int b) : base(b) { points = 0; }

    /// <summary>
    /// Moves the part of the model the base cannot see, and leaves the part it can. Both
    /// halves are stated, because a client holding an <c>Acct</c> needs the second one.
    /// </summary>
    [Requires("n >= 0")]
    [Requires("@this.ThePoints + n <= 2147483647")]
    [Ensures("@this.ThePoints == Old(@this.ThePoints) + n")]
    [Ensures("@this.TheBalance == Old(@this.TheBalance)")]
    public void Award(int n) { points = points + n; }

    [Frac("p")]
    [Requires("@this.ThePoints <= 2147483647")]
    [Ensures("Result == @this.ThePoints")]
    public int GetPoints() { return points; }
}
