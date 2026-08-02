using PalLang;

namespace PalCSharp.Tests;

[Spec]
public struct CursorModel
{
    public CellModel Pos;
    public CellModel Limit;
}

/// <summary>
/// The middle level. It owns two <c>Cell</c>s (R3.10b) and relates them, and it is itself
/// owned by <c>Ledger</c> — so the same class is both a composite and a component, which
/// is the only way to find out whether R3.10b composes with itself.
///
/// Nothing here mentions the level below the <c>Cell</c>s, and nothing mentions the level
/// above: <c>State</c> hands an owner this class's whole model without the owner ever
/// naming <c>pos</c>, exactly as <c>Cell.State</c> does for this class.
/// </summary>
public sealed class Cursor
{
    private Cell pos;
    private Cell limit;

    /// <summary>
    /// F17, a third time, and this is the place it bites. <c>pos.V &lt;= limit.V</c> is
    /// written as a <c>[Refine]</c> on the model rather than as an <c>[Invariant]</c>
    /// clause because <c>Ledger</c> needs it: an invariant clause is a <c>pure</c> conjunct
    /// <em>inside</em> this class's slprop, and an owner holds that slprop folded, so the
    /// conjunct never reaches it. A refinement travels with the model type instead, and is
    /// therefore available to this class, to its owner, and to its owner's clients alike.
    /// <c>Range</c> in <c>test/nested_class</c> may state the same kind of fact as an
    /// invariant only because nothing owns a <c>Range</c>.
    ///
    /// The bounds on the two cells are restated here for the same reason, even though
    /// <c>Cell</c> already refines its own model: a composite's model is built from the
    /// spec structs, and a refinement belongs to the <em>class</em> model type, so it does
    /// not survive being stored in an owner's model. Each level therefore republishes
    /// whatever its owners need. That is F17 applied compositionally, and it is the one
    /// cost R3.10b charges for depth.
    /// </summary>
    [Refine("0 <= Result.Pos.V && Result.Pos.V <= Result.Limit.V && Result.Limit.V <= 2147483647")]
    [Model]
    private CursorModel Model => new CursorModel { Pos = pos.State, Limit = limit.State };

    [Spec]
    public CursorModel State => Model;

    [Spec]
    public SpecInt At => Model.Pos.V;

    [Spec]
    public SpecInt Bound => Model.Limit.V;

    [Requires("0 <= bound")]
    [Ensures("@this.At == 0")]
    [Ensures("@this.Bound == bound")]
    public Cursor(int bound)
    {
        pos = new Cell(0);
        limit = new Cell(bound);
    }

    /// <summary>
    /// A mutation two levels deep. <c>pos</c> is folded here, and the <c>Cell</c> inside it
    /// is folded inside <em>that</em>, so this is an ordinary call whose precondition
    /// <c>@this.At &lt; 2147483647</c> comes from the invariant relating the two cells plus
    /// <c>Cell</c>'s refinement on <c>limit</c>'s model.
    /// </summary>
    [Requires("@this.At < @this.Bound")]
    [Ensures("@this.At == Old(@this.At) + 1")]
    [Ensures("@this.Bound == Old(@this.Bound)")]
    public void Step()
    {
        pos.Bump();
    }

    /// <summary>
    /// Read-only, and R4.11 has to follow the call two levels to see it: <c>Position</c>
    /// assigns nothing and calls <c>Cell.Value</c>, which assigns nothing either. Were the
    /// analysis to stop at the first call this would be a mutator, and <c>Ledger.Append</c>
    /// could not use its result to index an array.
    /// </summary>
    [Ensures("Result == @this.At")]
    public int Position()
    {
        return pos.Value();
    }
}
