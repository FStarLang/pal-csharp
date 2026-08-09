// EXPECT-PULSE: class_UpBox__inv var_b pre_b
// R9.15c. Converting a reference to a base *moves* the invariant onto the base-typed
// reference. `b` is a parameter, and R4.10's epilogue owes `b`'s invariant back to the
// caller, so `ViaBase` gives away something it has promised to return and its epilogue
// cannot be proved. Pulse says exactly that, naming the parameter and the invariant:
// `Cannot prove: Class_UpBox.class_UpBox__inv var_b pre_b`, mapped back to the `return` --
// which is the honest place for it, because the return is where the promise comes due.
//
// This was a frontend refusal, `PALCS0549`, and the case that stood here asserted that
// such a method "is a method whose specification cannot hold, whatever the emitter does".
// That claim is false, and it is worth recording how it was found to be false, because it
// is the reason the check is gone rather than merely relocated.
//
// A conversion is not one-way. R9.16 casts back down, and the generated downcast on a
// *leaf* proves reference identity outright -- `class_Box__from_Quadrilateral` ensures
// `r == reveal c` -- so `Shape s = b; ...; Box back = (Box)s;` really does return the
// resource to the very reference the parameter names. Running that program with the check
// disabled shows Pulse recovering `class_Box__inv var_back _` with `var_back == var_b`.
// What it does *not* recover is the model: an intermediate `__from_Shape` promises only
// `m == forget own`, and forgetting is not injective as far as F* is concerned, so the
// model the object came in at is lost. So the roundtrip fails today -- but for a
// different and much more specific reason than "the specification cannot hold", and one
// that is a gap in the encoding rather than a fact about the program.
//
// That is the whole argument for `test/pulse_refusals`, and it is the same one
// `AliasedObjects` makes about PALCS0520: a frontend refusal is an approximation, an
// approximation stands in front of the thing it approximates, and what stood behind this
// one was a limitation nobody could see because no program could reach it.
using PalLang;

public abstract class UpShape
{
    [Refine("Result >= 0")]
    [Model]
    protected abstract SpecInt Area { get; }

    [Spec]
    public SpecInt TheArea => Area;

    [Frac("p")]
    [Requires("@this.TheArea <= 2147483647")]
    [Ensures("Result == @this.TheArea")]
    public abstract int GetArea();
}

[Invariant("upSide >= 0")]
[Invariant("upSide * upSide <= 2147483647")]
public sealed class UpBox : UpShape
{
    private int upSide;

    /// <summary>R9.5, the abstraction function: this class's own model, over its fields.</summary>
    [Model]
    private SpecInt Side => upSide;

    /// <summary>R9.6, the forgetting function: the base's model, over this class's.</summary>
    protected override SpecInt Area => Side * Side;

    [Ensures("@this.TheArea == 0")]
    public UpBox()
    {
        upSide = 0;
    }

    public override int GetArea()
    {
        return upSide * upSide;
    }
}

public static class UpClient
{
    /// <summary>The same call at the base's own type is fine: nothing is converted.</summary>
    [Requires("s.TheArea <= 2147483647")]
    [Ensures("Result == s.TheArea")]
    public static int Measure(UpShape s)
    {
        return s.GetArea();
    }

    [Requires("b.TheArea <= 2147483647")]
    [Ensures("Result == b.TheArea")]
    public static int ViaBase(UpBox b)
    {
        UpShape s = b;
        // MARKER
        return s.GetArea();
    }
}
