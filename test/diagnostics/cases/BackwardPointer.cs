// EXPECT: PALCS0566
// R10.10. A back pointer is *constrained* by the invariant rather than owned by it, and the
// Pulse shape for that is pinned (test/pulse_facts/RecursiveFacts.fst §8). What is not
// pinned is the surface rule: a freshly allocated node's predecessor index has to come from
// somewhere, and no rule over C# yet says where. §0 rule 3 cuts both ways, so the refusal
// is written down rather than approximated by a guess in the emitter.
using PalLang;

public sealed class DoubleLink
{
    internal int value;
    internal DoubleLink? next;

    [Backward]
    internal DoubleLink? prev;

    [Model]
    private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Elements);

    [Spec]
    public SpecList<SpecInt> Elements => Items;
}
