// EXPECT: PALCS0565
// R10.9. The hierarchy encoding indexes an object by a vtable and reaches it through a
// `dyn`; the recursive encoding indexes it by its own model and reaches it through an
// `option`. Each is pinned on its own and neither has been probed against the other, so
// composing them would be the emitter inventing a rule rather than applying one.
//
// The class below is well formed under *both* sets of rules taken separately — it has its
// own `[Model]` over its fields (R10.5) and an `override` forgetting function to its base
// (R9.6) — so PALCS0565 is the only thing wrong with it. That is the point: the refusal is
// about the two encodings not composing, not about a malformed class.
using PalLang;

public abstract class Link
{
    [Model]
    protected abstract SpecList<SpecInt> Items { get; }

    [Spec]
    public SpecList<SpecInt> Elements => Items;
}

public sealed class ChainedLink : Link
{
    internal int value;
    internal ChainedLink? next;

    [Model]
    private SpecList<SpecInt> Chain => SpecList.Cons(value, next!.Chain);

    /// <summary>R9.6: the forgetting function to the base's model.</summary>
    protected override SpecList<SpecInt> Items => Chain;
}
