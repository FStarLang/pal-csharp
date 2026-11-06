// R27.46. A parameter at a supertype whose argument is exactly a translated class: inside,
// it is an object of that class, `as` and `is` are decided by the class, and every caller
// passes one.
// R27.47. `==` and `Equals` on comparers.
using System.Collections.Generic;
using PalLang;

public sealed class Cell
{
    private int value;

    [Model] private SpecInt Model => value;

    [Spec] public SpecInt SpecValue => Model;

    [Ensures("@this.SpecValue == v")]
    public Cell(int v)
    {
        value = v;
    }

    [Ensures("Result == @this.SpecValue")]
    public int Get() => value;

    // R27.45. A `return;` in a body after `: this(...)` returns the object.
    [Ensures("@this.SpecValue == (skip ? 0 : other.SpecValue)")]
    public Cell(Cell other, bool skip) : this(0)
    {
        if (skip)
        {
            return;
        }
        value = other.value;
    }

    // R27.45. Chaining to a constructor that hands `other` back hands it back too.
    [Ensures("@this.SpecValue == other.SpecValue")]
    [Ensures("other.SpecValue == Pal.Old(other.SpecValue)")]
    public Cell(Cell other) : this(other, false) { }

    [Ensures("Result == 14")]
    public static int Twice()
    {
        Cell a = new Cell(7);
        Cell b = new Cell(a);
        return a.Get() + b.Get();
    }

    // R27.48. What follows `Pal.Unreachable()` is proved dead and not translated.
    [Requires("x > 0")]
    [Ensures("Result == 1")]
    public static int Positive(int x)
    {
        if (x > 0)
        {
            return 1;
        }
        Pal.Unreachable();
        System.Console.WriteLine("unreachable");
        return 0;
    }

    [Ensures("Result == source.SpecValue")]
    public static int Read([Exactly(typeof(Cell))] object source)
    {
        Cell? cell = source as Cell;
        if (cell == null || source is string)
        {
            return -1;
        }
        return cell.Get();
    }

    [Ensures("Result")]
    public static bool IsCell([Exactly(typeof(Cell))] object source) => source is Cell && !(source is string);

    [Ensures("Result == 7")]
    public static int Client()
    {
        Cell c = new Cell(7);
        return Read(c);
    }

    // R27.47. Two comparers are one object exactly when they are one value.
    [Ensures("Result == (a == b)")]
    public static bool Same<T>(IComparer<T> a, IComparer<T> b) => a == b;

    // R27.47. `Equals` is a function of the two comparers, of which nothing else is known.
    [Ensures("Pal.Implies(a == b, Result)")]
    public static bool Equal<T>(IComparer<T> a, IComparer<T> b) => a == b || a.Equals(b);
}
