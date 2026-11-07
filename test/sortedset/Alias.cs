// R27.57. A sealed subclass that adds no state shares its base's representation: its
// objects are verified at their exact class, an override is called directly, and a base
// body that reaches an override is verified again at the subclass (a replica), with the
// subclass's extra `[Throws(..., At = ...)]` clause.
using System;
using PalLang;

[Spec]
public struct TallyModel<T>
{
    public SpecInt Count;
    public Seq<T> Items;
}

public class Tally<T>
{
    private int count;
    private T[] items = Array.Empty<T>();

    [Model] private TallyModel<T> Model => new TallyModel<T> { Count = count, Items = Pal.Contents(items) };

    [Spec] public SpecInt SpecCount => Model.Count;

    [Ensures("@this.SpecCount == 0")]
    public Tally() { }

    [Requires("@this.SpecCount < 1000")]
    [Ensures("Result && @this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
    [Throws(typeof(ArgumentException), "@this.SpecCount >= 10", At = typeof(CappedTally<>))]
    public bool Bump(T item) => BumpCore(item);

    [Requires("@this.SpecCount < 1000")]
    [Ensures("Result && @this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
    internal virtual bool BumpCore(T item)
    {
        count++;
        return true;
    }

    [Ensures("Result == @this.SpecCount")]
    public int Count => count;
}

public sealed class CappedTally<T> : Tally<T>
{
    [Ensures("@this.SpecCount == 0")]
    public CappedTally() { }

    [Requires("@this.SpecCount < 1000")]
    [Ensures("Result && @this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
    [Throws(typeof(ArgumentException), "@this.SpecCount >= 10")]
    internal override bool BumpCore(T item)
    {
        if (Count >= 10) throw new ArgumentException("full");
        return base.BumpCore(item);
    }
}

public sealed class TallyHolder
{
    private readonly CappedTally<int> tally;

    [Model] private SpecInt Model => tally.SpecCount;

    [Spec] public SpecInt SpecCount => Model;

    [Ensures("@this.SpecCount == 0")]
    public TallyHolder()
    {
        tally = new CappedTally<int>();
    }

    [Requires("@this.SpecCount < 10")]
    [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
    public void Add(int x)
    {
        tally.Bump(x);
    }

    [Ensures("Result == @this.SpecCount")]
    public int Count() => tally.Count;
}
