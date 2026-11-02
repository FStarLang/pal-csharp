using System;
using System.Numerics;
using PalLang;

// R20.12. A class with no model is translated method by method, its state its context.
[assembly: TranslateAnnotatedOnly]
[assembly: IncludePulseFile("Shapes.fst")]
[assembly: SpecBinding("T:System.Numerics.BigInteger", "Prims.int")]
[assembly: SpecBinding("M:System.Numerics.BigInteger.op_LessThan(System.Numerics.BigInteger,System.Numerics.BigInteger)", "Shapes.big_less")]

namespace PalCSharp.Tests;

/// <summary>R21.4. An enum whose constants are the constructors of an F* enumeration.</summary>
[SpecType("Shapes.color")]
public enum Color { Red, Green, Blue }

/// <summary>
/// R21.1. A closed record hierarchy: an abstract record with a private constructor, whose
/// sealed nested records are the constructors of <c>Shapes.shape</c>. Each case's positional
/// parameters are the constructor's arguments, in order.
/// </summary>
[SpecType("Shapes.shape", Nullable = true)]
public abstract record Shape
{
    private Shape() { }

    public sealed record Dot(Color C) : Shape;
    public sealed record Bar(BigInteger Length, bool Solid) : Shape;
    public sealed record Pair(Shape Left, Shape Right) : Shape;

    [SpecOp("Shapes.next")] public static Color Next(Color c) => throw new InvalidOperationException();
    [SpecOp("Shapes.shade")] public static Color? Shade(Shape s) => throw new InvalidOperationException();
    [SpecOp("Shapes.longer")] public static bool Longer(Shape s, Shape t) => throw new InvalidOperationException();
    [SpecOp("Shapes.first")] public static Shape First(Shape s) => throw new InvalidOperationException();
    [SpecOp("Shapes.solid_bar")] public static Shape? SolidBar(Shape s) => throw new InvalidOperationException();
    [SpecOp("Shapes.paint")] public static Shape Paint(IPalette p, Shape s) => throw new InvalidOperationException();
    [SpecOp("Shapes.Dot?")] public static bool IsDot(Shape s) => throw new InvalidOperationException();
}

/// <summary>An opaque specification type whose one method is a model function.</summary>
[SpecType("Shapes.palette")]
public interface IPalette
{
    [SpecOp("Shapes.pick")] Color Pick(Color c);
}

/// <summary>R20.12a. <c>palette</c> is a captured primary-constructor parameter.</summary>
public sealed class Shapes(IPalette palette)
{
    /// <summary>R21.6. A switch over enum constants; the discard arm is unreachable.</summary>
    [Ensures("Result == Shape.Next(c)")]
    public static Color Next(Color c) => c switch
    {
        Color.Red => Color.Green,
        Color.Green => Color.Blue,
        Color.Blue => Color.Red,
        _ => throw new ArgumentOutOfRangeException(nameof(c))
    };

    /// <summary>A declaration pattern, and a projection of the case it narrowed to.</summary>
    [Ensures("Result == Shape.Shade(s)")]
    public static Color? Shade(Shape s) => s is Shape.Dot d ? d.C : null;

    /// <summary>A tuple switch of property patterns, through a bound operator (R21.5).</summary>
    [Ensures("Result == Shape.Longer(s, t)")]
    public static bool Longer(Shape s, Shape t) => (s, t) switch
    {
        (Shape.Bar { Length: var n }, Shape.Bar { Length: var m }) => n < m,
        _ => false
    };

    /// <summary><c>as</c>, then a nullable local C# knows is not null (R21.9).</summary>
    [Ensures("Result == Shape.First(s)")]
    public static Shape First(Shape s)
    {
        var p = s as Shape.Pair;
        if (p is null) return s;
        return p.Left;
    }

    /// <summary>A constant subpattern, and a case built back up into a nullable result.</summary>
    [Ensures("Result == Shape.SolidBar(s)")]
    public static Shape? SolidBar(Shape s) => s switch
    {
        Shape.Bar { Solid: true } b => new Shape.Bar(b.Length, true),
        _ => null
    };

    /// <summary>The captured parameter, read from an instance method.</summary>
    [Ensures("Result == Shape.Paint(palette, s)")]
    public Shape Paint(Shape s) => s switch
    {
        Shape.Dot { C: var c } => new Shape.Dot(palette.Pick(c)),
        _ => s
    };

    /// <summary>A library exception, thrown where the precondition makes it unreachable.</summary>
    [Requires("Shape.IsDot(s)")]
    [Ensures("Result == Shape.Shade(s).Value")]
    public static Color ColorOf(Shape s)
    {
        if (s is Shape.Dot d) return d.C;
        throw new ArgumentException("Not a dot.", nameof(s));
    }

    /// <summary>A parameter named <c>result</c> is not the <c>returns</c> binder (R4.4).</summary>
    [Ensures("Result == Shape.First(result)")]
    public static Shape Unwrap(Shape result) => result is Shape.Pair p ? p.Left : result;
}
