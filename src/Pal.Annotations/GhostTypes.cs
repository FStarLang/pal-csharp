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
