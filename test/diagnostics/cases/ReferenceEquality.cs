// EXPECT: PALCS0593
// R18.1. R6.4 gives an operator a meaning only at a primitive type. Applied to two class
// references, `==` was emitted as `I32.eq` over two boxes — ill-typed F*, produced with
// `0 error(s)`. Object identity has no rule: two equal references are not interchangeable
// in a context that owns one of them.
using PalLang;

public sealed class Node
{
    private int v;

    [Model]
    private SpecInt TheV => v;

    public Node(int x)
    {
        this.v = x;
    }
}

public static class Same
{
    public static bool Eq(Node p, Node q)
    {
        return p == q;
    }
}
