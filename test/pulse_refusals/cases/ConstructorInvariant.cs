// EXPECT-PULSE: class_ConstructorInvariant__model__pred
// R4.12. The invariant has to be *established* somewhere, and that somewhere is the
// constructor. This one stores whatever it is given, so a negative argument produces an
// object that never satisfied the invariant it advertises -- which is the one failure that
// would poison every method on the class at once, since they all get to assume it.
using PalLang;

[Invariant("balance >= 0")]
public sealed class ConstructorInvariant
{
    private int balance;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Bal => balance;

    [Spec]
    public SpecInt TheBalance => Bal;

    [Ensures("@this.TheBalance == b")]
    // MARKER
    public ConstructorInvariant(int b) { balance = b; }
}
