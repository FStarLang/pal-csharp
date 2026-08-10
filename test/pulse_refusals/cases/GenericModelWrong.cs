// EXPECT-PULSE: spec_GenericModelWrong_Elements pre_this @
// §15. The obligation over a class parameterised by a type. `Push` prepends and the
// contract claims it appends, which for a list of `T` is a claim the prover has to reject
// without knowing anything about `T` at all -- that is the point of R15.5: an unconstrained
// parameter has no model to convert to, so the model of a `Cell<T>` is a `SpecList<T>` and
// the two sides are simply different lists.
//
// A generic negative case earns its place because the machinery differs: the binders are
// the class's (R15.1) and every predicate is applied at them (R15.3), so a failure here
// exercises a path that no monomorphic case reaches.
using PalLang;

public sealed class Cell<T>
{
    internal T value;
    internal Cell<T>? next;

    [Model]
    private SpecList<T> Items => SpecList.Cons(value, next!.Items);

    [Spec]
    public SpecList<T> Elements => Items;

    [Ensures("@this.Elements == SpecList.Cons(v, n.Elements)")]
    public Cell(T v, Cell<T>? n)
    {
        value = v;
        next = n;
    }
}

public sealed class GenericModelWrong<T>
{
    private Cell<T>? head;

    [Model]
    private SpecList<T> Items => head!.Elements;

    [Spec]
    public SpecList<T> Elements => Items;

    [Ensures("@this.Elements == SpecList.Empty<T>()")]
    public GenericModelWrong()
    {
        head = null;
    }

    [Ensures("@this.Elements == SpecList.Append(Old(@this.Elements), SpecList.Cons(v, SpecList.Empty<T>()))")]
    // MARKER
    public void Push(T v)
    {
        head = new Cell<T>(v, head);
    }
}
