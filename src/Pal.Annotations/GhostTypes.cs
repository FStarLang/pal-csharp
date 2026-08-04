using System;
using System.Numerics;

namespace PalLang;

/// <summary>
/// A ghost (proof-only) parameter of type <typeparamref name="T"/>.
/// </summary>
/// <remarks>
/// Declare it as an optional parameter so callers may omit it:
/// <code>static int Foo(int x, Ghost&lt;Seq&lt;int&gt;&gt; s = default)</code>
/// The struct is empty, so it occupies no space and <c>default</c> allocates
/// nothing. The translator erases it to a Pulse implicit <c>(#s: erased t)</c>.
/// </remarks>
public readonly struct Ghost<T>
{
    /// <summary>The ghost value. Specification-only; throws if read at runtime.</summary>
    public T Value => throw new InvalidOperationException(
        "Ghost<T>.Value is a specification-only construct and has no runtime meaning.");

    public static implicit operator Ghost<T>(T value) => default;
}

/// <summary>
/// An unbounded specification integer, translated to F*'s <c>int</c>.
/// Use it in specifications to reason without overflow obligations.
/// </summary>
public readonly struct SpecInt(BigInteger value) : IEquatable<SpecInt>
{
    public BigInteger Value { get; } = value;

    public static implicit operator SpecInt(int v) => new(v);
    public static implicit operator SpecInt(long v) => new(v);
    public static implicit operator SpecInt(BigInteger v) => new(v);

    public static SpecInt operator +(SpecInt a, SpecInt b) => new(a.Value + b.Value);
    public static SpecInt operator -(SpecInt a, SpecInt b) => new(a.Value - b.Value);
    public static SpecInt operator *(SpecInt a, SpecInt b) => new(a.Value * b.Value);
    public static SpecInt operator /(SpecInt a, SpecInt b) => new(a.Value / b.Value);
    public static SpecInt operator %(SpecInt a, SpecInt b) => new(a.Value % b.Value);

    public static bool operator <(SpecInt a, SpecInt b) => a.Value < b.Value;
    public static bool operator >(SpecInt a, SpecInt b) => a.Value > b.Value;
    public static bool operator <=(SpecInt a, SpecInt b) => a.Value <= b.Value;
    public static bool operator >=(SpecInt a, SpecInt b) => a.Value >= b.Value;
    public static bool operator ==(SpecInt a, SpecInt b) => a.Value == b.Value;
    public static bool operator !=(SpecInt a, SpecInt b) => a.Value != b.Value;

    public bool Equals(SpecInt other) => Value == other.Value;
    public override bool Equals(object? obj) => obj is SpecInt s && Equals(s);
    public override int GetHashCode() => Value.GetHashCode();
    public override string ToString() => Value.ToString();
}

/// <summary>
/// A non-negative specification integer, translated to F*'s <c>nat</c>.
/// </summary>
public readonly struct SpecNat(BigInteger value) : IEquatable<SpecNat>
{
    public BigInteger Value { get; } = value >= BigInteger.Zero
        ? value
        : throw new ArgumentOutOfRangeException(nameof(value), "SpecNat must be non-negative.");

    public static implicit operator SpecNat(int v) => new(v);
    public static implicit operator SpecInt(SpecNat n) => new(n.Value);

    public static SpecNat operator +(SpecNat a, SpecNat b) => new(a.Value + b.Value);
    public static SpecNat operator *(SpecNat a, SpecNat b) => new(a.Value * b.Value);

    public static bool operator <(SpecNat a, SpecNat b) => a.Value < b.Value;
    public static bool operator >(SpecNat a, SpecNat b) => a.Value > b.Value;
    public static bool operator <=(SpecNat a, SpecNat b) => a.Value <= b.Value;
    public static bool operator >=(SpecNat a, SpecNat b) => a.Value >= b.Value;
    public static bool operator ==(SpecNat a, SpecNat b) => a.Value == b.Value;
    public static bool operator !=(SpecNat a, SpecNat b) => a.Value != b.Value;

    public bool Equals(SpecNat other) => Value == other.Value;
    public override bool Equals(object? obj) => obj is SpecNat s && Equals(s);
    public override int GetHashCode() => Value.GetHashCode();
    public override string ToString() => Value.ToString();
}

/// <summary>
/// A ghost immutable sequence, translated to F*'s <c>Seq.seq</c>. Obtain one
/// from an array with <see cref="Pal.Contents{T}(T[])"/>.
/// </summary>
public readonly struct Seq<T>
{
    private static Exception Ghost() => new InvalidOperationException(
        "Seq<T> is a specification-only construct and has no runtime meaning.");

    public int Length => throw Ghost();
    public T this[int index] => throw Ghost();

    /// <summary>
    /// Indexing by an unbounded specification integer. The overload exists so that a
    /// recursive <c>[Spec]</c> function, whose parameters are naturally <c>SpecInt</c>,
    /// can index without a cast.
    /// </summary>
    public T this[SpecInt index] => throw Ghost();

    public static bool operator ==(Seq<T> a, Seq<T> b) => throw Ghost();
    public static bool operator !=(Seq<T> a, Seq<T> b) => throw Ghost();

    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

/// <summary>
/// A separation-logic proposition. <c>*</c> is Pulse's separating conjunction
/// <c>**</c>.
/// </summary>
public readonly struct SlProp
{
    private static Exception Ghost() => new InvalidOperationException(
        "SlProp is a specification-only construct and has no runtime meaning.");

    /// <summary>The empty resource, Pulse's <c>emp</c>.</summary>
    public static SlProp Emp => default;

    /// <summary>Separating conjunction (Pulse <c>**</c>).</summary>
    public static SlProp operator *(SlProp left, SlProp right) => throw Ghost();
}

/// <summary>
/// A ghost inductive list, translated to F*'s <c>list</c> (R10.5).
/// </summary>
/// <remarks>
/// Its purpose is to be the <em>model</em> of a recursive class. The <c>[Model]</c> member
/// of a class with a <c>C? next</c> field is written as a constructor application over the
/// fields — <c>SpecList.Cons(value, next.Items)</c> — and the translator reads that
/// equation backwards to obtain the class's inductive ownership predicate. The user never
/// writes the predicate, and never writes the lemmas that take it apart.
/// </remarks>
public readonly struct SpecList<T>
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecList<T> is a specification-only construct and has no runtime meaning.");

    /// <summary>The number of elements, F*'s <c>List.Tot.length</c>.</summary>
    public SpecInt Length => throw Ghost();

    /// <summary>True of the empty list.</summary>
    public bool IsEmpty => throw Ghost();

    /// <summary>The first element; specification-only, and meaningful only when non-empty.</summary>
    public T Head => throw Ghost();

    /// <summary>Everything but the first element.</summary>
    public SpecList<T> Tail => throw Ghost();

    public T this[SpecInt index] => throw Ghost();

    public static bool operator ==(SpecList<T> a, SpecList<T> b) => throw Ghost();
    public static bool operator !=(SpecList<T> a, SpecList<T> b) => throw Ghost();

    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

/// <summary>The constructors of <see cref="SpecList{T}"/>.</summary>
public static class SpecList
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecList is a specification-only construct and has no runtime meaning.");

    /// <summary>The empty list, F*'s <c>[]</c>. What a null reference denotes (R10.5).</summary>
    public static SpecList<T> Empty<T>() => throw Ghost();

    /// <summary>F*'s <c>hd :: tl</c>.</summary>
    public static SpecList<T> Cons<T>(T head, SpecList<T> tail) => throw Ghost();

    /// <summary>F*'s <c>List.Tot.append</c>.</summary>
    public static SpecList<T> Append<T>(SpecList<T> left, SpecList<T> right) => throw Ghost();
}

/// <summary>
/// A ghost binary tree, translated to <c>Pulse.Lib.CSharp.Tree.tree</c> (R10.5).
/// The model of a class with two recursive fields.
/// </summary>
public readonly struct SpecTree<T>
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecTree<T> is a specification-only construct and has no runtime meaning.");

    /// <summary>The number of interior nodes.</summary>
    public SpecInt Size => throw Ghost();

    /// <summary>True of the empty tree.</summary>
    public bool IsLeaf => throw Ghost();

    public static bool operator ==(SpecTree<T> a, SpecTree<T> b) => throw Ghost();
    public static bool operator !=(SpecTree<T> a, SpecTree<T> b) => throw Ghost();

    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

/// <summary>The constructors of <see cref="SpecTree{T}"/>.</summary>
public static class SpecTree
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecTree is a specification-only construct and has no runtime meaning.");

    /// <summary>The empty tree. What a null reference denotes (R10.5).</summary>
    public static SpecTree<T> Leaf<T>() => throw Ghost();

    /// <summary>An interior node.</summary>
    public static SpecTree<T> Branch<T>(SpecTree<T> left, T value, SpecTree<T> right) =>
        throw Ghost();

    /// <summary>
    /// Binary-search-tree insertion, <c>Pulse.Lib.CSharp.Tree.insert_int</c>. It is the
    /// <em>model</em> of the destructive operation, supplied by the library rather than
    /// written as a user <c>[Spec]</c> function, so that a C# implementation can be proved
    /// equal to it.
    /// </summary>
    public static SpecTree<SpecInt> Insert(SpecTree<SpecInt> tree, SpecInt value) =>
        throw Ghost();
}
