using PalLang;

namespace PalCSharp.Tests;

[Spec]
public struct LedgerModel
{
    public CursorModel Cursor;
    public Seq<int> Slots;
}

/// <summary>
/// R3.10a and R3.10b in one class: <c>Ledger</c> owns an array <em>and</em> an object, and
/// its invariant ties them together — the cursor's bound is the array's length. The two
/// rules are the same rule with one word changed, so the invariant carries the array's
/// <em>contents</em> and the object's <em>model</em>, and inside a method's window the
/// array is unfolded while the object stays folded.
///
/// The hierarchy is three deep: a client of <c>Ledger</c> reasons about a sequence and a
/// count, and never learns that the count lives in a <c>Cell</c> inside a <c>Cursor</c>.
/// </summary>
[Invariant("cursor.Bound == slots.Length")]
public sealed class Ledger
{
    private Cursor cursor;
    private int[] slots;

    /// <summary>
    /// What a client of a three-level hierarchy needs to know about the bottom of it:
    /// the count is a non-negative index into the array. Both facts exist two levels down
    /// — in <c>Cell</c>'s refinement and in <c>Cursor</c>'s — and both have to be
    /// republished here, because a model built from spec structs does not inherit the
    /// refinements of the class models it summarises (F17).
    /// </summary>
    [Refine("0 <= Result.Cursor.Pos.V && Result.Cursor.Pos.V <= Result.Slots.Length")]
    [Model]
    private LedgerModel Model => new LedgerModel
    {
        Cursor = cursor.State,
        Slots = Pal.Contents(slots),
    };

    [Spec]
    public SpecInt Count => Model.Cursor.Pos.V;

    [Spec]
    public SpecInt Capacity => Model.Slots.Length;

    [Spec]
    public Seq<int> Data => Model.Slots;

    [Requires("0 <= capacity")]
    [Ensures("@this.Count == 0")]
    [Ensures("@this.Capacity == capacity")]
    public Ledger(int capacity)
    {
        slots = new int[capacity];
        cursor = new Cursor(capacity);
    }

    /// <summary>
    /// One method writing both kinds of field. <c>slots[at] = value</c> unsettles the
    /// array's contents and nothing else; <c>cursor.Step()</c> unsettles the cursor's model
    /// and nothing else. That the array survives a call on the object, and the object
    /// survives a write to the array, is separation and not a rule anyone had to state.
    /// </summary>
    [Requires("@this.Count < @this.Capacity")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Data[Old(@this.Count)] == value")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < Old(@this.Count), @this.Data[i] == Old(@this.Data)[i]))")]
    public void Append(int value)
    {
        int at = cursor.Position();
        slots[at] = value;
        cursor.Step();
    }

    [Requires("0 <= i && i < @this.Count")]
    [Ensures("Result == @this.Data[i]")]
    public int Get(int i)
    {
        return slots[i];
    }

    [Ensures("Result == @this.Count")]
    public int Size()
    {
        return cursor.Position();
    }
}
