// EXPECT: PALCS0571
// R11.3. A `[SpecCtor]` builds a value of the specification type it constructs, so it
// has to be a static method returning that type. The method below returns an `int`, so
// the F* application the translator would emit is ill-typed — and the C# signature
// would be saying something the emitted F* does not.
using PalLang;

[SpecType("Misplaced.thing")]
public sealed class MisplacedThing
{
}

public static class MisplacedOps
{
    [SpecCtor("Misplaced.Mk", Empty = true)]
    public static int Make() => 0;
}
