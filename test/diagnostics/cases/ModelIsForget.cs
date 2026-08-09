// EXPECT: PALCS0543
// R9.5 and R9.6 are two functions over two different domains. The abstraction function
// reads the *fields* and says what this class's model is; the forgetting function reads
// this class's *model* and says what the base's model is. A subclass of an abstract class
// must write both, and it writes them as two members: one new member marked `[Model]`, and
// the `override` of the base's `[Model]` member.
//
// Marking the override itself `[Model]` asks one member to be both. Before this refusal
// existed the request was accepted and lowered twice -- once against the fields, which
// worked, and once against the model, which did not -- and what the reader saw was
// `PALCS0001: the expression 'mdSide' is not supported`, pointing at a field that is
// perfectly supported. That message is true of the second lowering and useless to anyone.
using PalLang;

public abstract class MdShape
{
    [Refine("Result >= 0")]
    [Model]
    protected abstract SpecInt MdArea { get; }

    [Spec]
    public SpecInt TheMdArea => MdArea;
}

[Invariant("mdSide >= 0")]
[Invariant("mdSide * mdSide <= 2147483647")]
public sealed class MdSquare : MdShape
{
    private int mdSide;

    [Model]
    protected override SpecInt MdArea => mdSide * mdSide;

    [Ensures("@this.TheMdArea == 0")]
    public MdSquare()
    {
        mdSide = 0;
    }
}
