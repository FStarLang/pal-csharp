// EXPECT-PULSE: Class_ListModelWrong.spec_ListModelWrong_Elements pre_this
// §10. The same shape of failure as `PostconditionFalse`, but over a recursive structure,
// so the obligation runs through the inductive predicate instead of over a flat sequence.
// `Push` really does prepend, and its contract claims the list comes out unchanged.
//
// A negative suite that only ever breaks arithmetic only tests the arithmetic. This case is
// here to check that the §10 machinery -- the induction read off the model, the fold at the
// exit -- also refuses a false claim, and refuses it against the C# that made it. Every
// other line is `test/linked_list`'s, unaltered, so what fails is the contract and not the
// scaffolding around it.
using PalLang;

public sealed class Node
{
    internal int value;
    internal Node? next;

    // R10.5. The `!` is what makes the model total: a null `next` denotes the empty list.
    [Model]
    private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Items);

    [Spec]
    public SpecList<SpecInt> Elements => Items;

    [Ensures("@this.Elements == SpecList.Cons(v, n.Elements)")]
    public Node(int v, Node? n)
    {
        value = v;
        next = n;
    }
}

public sealed class ListModelWrong
{
    private Node? head;

    [Model]
    private SpecList<SpecInt> Items => head!.Elements;

    [Spec]
    public SpecList<SpecInt> Elements => Items;

    [Ensures("@this.Elements == SpecList.Empty<SpecInt>()")]
    public ListModelWrong()
    {
        head = null;
    }

    [Ensures("@this.Elements == Old(@this.Elements)")]
    // MARKER
    public void Push(int v)
    {
        head = new Node(v, head);
    }
}
