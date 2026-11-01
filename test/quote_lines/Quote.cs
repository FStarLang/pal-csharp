using System.Collections.Generic;
using System.Linq;
using PalLang;

// Only annotated members are translated (doc/translation.md R20.1): `Untranslated` below
// uses a type pal-csharp has no model of, and is not looked at.
[assembly: TranslateAnnotatedOnly]
[assembly: IncludePulseFile("Lines.fst")]

[SpecType("Lines.line")]
public sealed class Line
{
    [SpecOp("Lines.line_price")]
    public decimal Price { get; set; }

    [SpecOp("Lines.line_cap")]
    public decimal? Cap { get; set; }

    [SpecOp("Lines.capped")]
    public static bool Capped(Line l) => throw new System.InvalidOperationException();

    [SpecOp("Lines.by_price")]
    public static Seq<Line> ByPrice(Seq<Line> s) => throw new System.InvalidOperationException();
}

public static class Untranslated
{
    public static int Size(Dictionary<string, int> d) => d.Count;
}

public static class Quote
{
    // foreach over a list, with the position of the current element named by Pal.Index.
    [Ensures("Pal.Implies(Result, Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Contents(lines).Length, Line.Capped(Pal.Contents(lines)[j]))))")]
    public static bool AllCapped([Frac("p")] IList<Line> lines)
    {
        bool ok = true;
        foreach (var line in lines)
        {
            Pal.Invariant(Pal.Implies(ok, Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Index(line),
                Line.Capped(Pal.Contents(lines)[j])))));
            if (line.Cap.HasValue && line.Price > line.Cap.Value)
            {
                ok = false;
            }
        }
        return ok;
    }

    // A nullable decimal: `x` converts implicitly to `decimal?`.
    [Ensures("Result.HasValue")]
    public static decimal? Clamp(decimal x, decimal? cap)
    {
        if (cap.HasValue && x > cap.Value)
        {
            return cap.Value;
        }
        return x;
    }

    [Ensures("Result == (code == \"open\")")]
    public static bool IsOpen(string code) => code == "open";

    // LINQ OrderBy into a local list, which the method owns and drops.
    [Ensures("Result == Pal.Contents(lines).Length")]
    public static int SortedCount([Frac("p")] IList<Line> lines)
    {
        var sorted = lines.OrderBy(l => l.Price).ToList();
        return sorted.Count;
    }
}
