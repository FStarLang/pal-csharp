// EXPECT: PALCS0565
// R10.9. The hierarchy encoding indexes an object by a vtable and reaches it through a
// `dyn`; the recursive encoding indexes it by its own model and reaches it through an
// `option`. Each is pinned on its own and neither has been probed against the other, so
// composing them would be the emitter inventing a rule rather than applying one.
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
    protected override SpecList<SpecInt> Items => SpecList.Cons(value, next!.Elements);
}
