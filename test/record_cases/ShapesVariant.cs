using System;
using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's contortion detector, for §21: <see cref="Shapes"/> again, with every match
/// written another way -- conditionals for switches, switches for conditionals, negated
/// tests, nested tests for tuple patterns, positional components read as properties.
/// </summary>
public sealed class ShapesVariant(IPalette colors)
{
    [Ensures("Result == Shape.Next(c)")]
    public static Color Next(Color c) =>
        c == Color.Red ? Color.Green : c == Color.Green ? Color.Blue : Color.Red;

    [Ensures("Result == Shape.Shade(s)")]
    public static Color? Shade(Shape s) => s switch
    {
        Shape.Dot { C: var c } => c,
        _ => null
    };

    [Ensures("Result == Shape.Longer(s, t)")]
    public static bool Longer(Shape s, Shape t)
    {
        if (s is not Shape.Bar a) return false;
        if (t is not Shape.Bar b) return false;
        return a.Length < b.Length;
    }

    [Ensures("Result == Shape.First(s)")]
    public static Shape First(Shape s) => s switch
    {
        Shape.Pair { Left: var left } => left,
        Shape.Dot or Shape.Bar => s,
        _ => s
    };

    [Ensures("Result == Shape.SolidBar(s)")]
    public static Shape? SolidBar(Shape s)
    {
        Shape? found = null;
        if (s is Shape.Bar b && b.Solid) found = new Shape.Bar(b.Length, b.Solid);
        return found;
    }

    [Ensures("Result == Shape.Paint(colors, s)")]
    public Shape Paint(Shape s)
    {
        if (s is not Shape.Dot d) return s;
        var picked = colors.Pick(d.C);
        return new Shape.Dot(picked);
    }
}
