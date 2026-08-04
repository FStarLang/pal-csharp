// EXPECT: PALCS0572
// R11.5. A recursive class's null reference has to denote *something* in the model, and
// the encoding needs to know exactly which constructor that is: `class__cases` says
// `Some? x <==> Cons? m`, so the nil side has to be a single, named alternative.
//
// The specification type below is otherwise well formed — it has a constructor, an
// operation, and an F* type — but no `[SpecCtor(Empty = true)]`, so there is no answer
// to what an empty chain means.
using PalLang;

[SpecType("NoEmpty.run")]
public sealed class RunOf
{
}

public static class RunOps
{
    [SpecCtor("NoEmpty.Step")]
    public static RunOf Step(SpecInt head, RunOf rest) => throw new System.InvalidOperationException();

    [SpecOp("NoEmpty.len")]
    public static SpecInt Length(this RunOf r) => throw new System.InvalidOperationException();
}

public sealed class RunLink
{
    internal int item;
    internal RunLink? next;

    [Model]
    private RunOf Run => RunOps.Step(item, next!.Run);

    [Spec]
    public RunOf Trace => Run;
}
