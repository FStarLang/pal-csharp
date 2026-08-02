using PalLang;

namespace PalCSharp.Tests;

/// <summary>The same composite model, declared the other way round.</summary>
[Spec]
public struct JournalModel
{
    public Seq<int> Entries;
    public CursorModel Head;
}

/// <summary>
/// §7.2's variant detector for a class owning an array <em>and</em> an object. The same
/// class as <c>Ledger</c>, written every other way C# allows: members in the opposite
/// order, both fields renamed, the model's two components declared the other way round,
/// <c>this.</c> written out, the invariant's equation reversed, expression bodies where
/// <c>Ledger</c> uses blocks, and the appended index taken from a local written in two
/// steps rather than one.
///
/// Modulo names the emitted Pulse is the same, and every difference that remains is one
/// this file asked for: the array's resource and the object's resource appear in the order
/// the fields are declared in. What matters is what does <em>not</em> differ — the array is
/// unfolded and the object is folded either way, a write to one settles nothing about the
/// other either way, and the refinements each level republishes are the same refinements.
/// </summary>
[Invariant("log.Length == head.Bound")]
public sealed class Journal
{
    [Ensures("Result == @this.Used")]
    public int Size() => this.head.Position();

    [Requires("0 <= i && i < @this.Used")]
    [Ensures("Result == @this.Entries[i]")]
    public int Get(int i) => this.log[i];

    [Requires("@this.Used < @this.Room")]
    [Ensures("@this.Used == Old(@this.Used) + 1")]
    [Ensures("@this.Room == Old(@this.Room)")]
    [Ensures("@this.Entries[Old(@this.Used)] == value")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < Old(@this.Used), @this.Entries[i] == Old(@this.Entries)[i]))")]
    public void Append(int value)
    {
        int at;
        at = this.head.Position();
        this.log[at] = value;
        this.head.Step();
    }

    [Requires("0 <= room")]
    [Ensures("@this.Used == 0")]
    [Ensures("@this.Room == room")]
    public Journal(int room)
    {
        this.head = new Cursor(room);
        this.log = new int[room];
    }

    [Spec]
    public Seq<int> Entries => this.Model.Entries;

    [Spec]
    public SpecInt Room => this.Model.Entries.Length;

    [Spec]
    public SpecInt Used => this.Model.Head.Pos.V;

    [Refine("Result.Head.Pos.V <= Result.Entries.Length && 0 <= Result.Head.Pos.V")]
    [Model]
    private JournalModel Model => new JournalModel
    {
        Entries = Pal.Contents(this.log),
        Head = this.head.State,
    };

    private int[] log;
    private Cursor head;
}
