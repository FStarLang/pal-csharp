using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A leaf (R9.14): <c>sealed</c>, with a representation of its own. Everything about the
/// M2 encoding still holds inside it — the fields, the abstraction function, the
/// <c>[Invariant]</c>, the <c>[Refine]</c> — and the hierarchy adds a wrapper round it.
/// </summary>
[Invariant("side >= 1")]
public sealed class Square : Shape
{
    private int side;

    /// <summary>Square's own model. It knows more than a <c>Shape</c> does.</summary>
    [Refine("Result >= 1")]
    [Model]
    private SpecInt Side => side;

    /// <summary>
    /// The forgetting function (R9.6): <c>Shape</c>'s model written in terms of
    /// <c>Square</c>'s. It is an ordinary C# <c>override</c> and needs no new attribute —
    /// which is the point, since a subclass saying what its parent's model is *is* an
    /// override of the parent's model member.
    /// </summary>
    protected override SpecInt Area => Side * Side;

    [Requires("n >= 1")]
    [Requires("n * n <= 2147483647")]
    [Ensures("@this.SideLength == n")]
    public Square(int n)
    {
        side = n;
    }

    /// <summary>An observation of Square's own model, unavailable through a <c>Shape</c>.</summary>
    [Spec]
    public SpecInt SideLength => Side;

    /// <summary>
    /// An <c>override</c> carries no contract of its own (R9.7): the contract was written
    /// once, on <c>Shape.GetArea</c>, and this is checked against it at <em>Shape</em>'s
    /// model. Restating it here would be a repetition or a Liskov violation.
    /// </summary>
    public override int GetArea()
    {
        return side * side;
    }

    public override void Double()
    {
        side = 2 * side;
    }
}
