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

    /// <summary>
    /// The first <paramref name="count"/> elements (R15.7). Total: a negative count takes
    /// nothing and an over-long one takes everything, so the term is meaningful wherever a
    /// C# <c>int</c> is, and the bound the caller cares about is stated in its own
    /// <c>[Requires]</c> rather than smuggled into the type of this operation.
    /// </summary>
    public static SpecList<T> Take<T>(SpecList<T> list, SpecInt count) => throw Ghost();

    /// <summary>Everything but the first <paramref name="count"/> elements (R15.7).</summary>
    public static SpecList<T> Drop<T>(SpecList<T> list, SpecInt count) => throw Ghost();

    /// <summary>
    /// <paramref name="list"/> with <paramref name="value"/> spliced in as element
    /// <paramref name="index"/> (R15.7).
    /// </summary>
    public static SpecList<T> InsertAt<T>(SpecList<T> list, SpecInt index, T value) => throw Ghost();

    /// <summary><paramref name="list"/> without element <paramref name="index"/> (R15.7).</summary>
    public static SpecList<T> RemoveAt<T>(SpecList<T> list, SpecInt index) => throw Ghost();

    /// <summary>The elements in the opposite order (R15.7).</summary>
    public static SpecList<T> Reverse<T>(SpecList<T> list) => throw Ghost();
}

/// <summary>
/// R27.21. The heap of the region of the <c>[Region]</c> class <typeparamref name="K"/>: a
/// value, so it can be snapshotted in a <c>Ghost</c> local and passed to a
/// <see cref="RegionOpAttribute"/> operation. <c>Pal.Heap&lt;K&gt;()</c> names the current one.
/// </summary>
[SpecType("Pulse.Lib.CSharp.Region.heap")]
public readonly struct SpecHeap<K> where K : class
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecHeap<K> is a specification-only construct and has no runtime meaning.");

    public static bool operator ==(SpecHeap<K> a, SpecHeap<K> b) => throw Ghost();
    public static bool operator !=(SpecHeap<K> a, SpecHeap<K> b) => throw Ghost();

    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

/// <summary>
/// A ghost binary tree, the model of a class with two recursive fields (R10.5).
///
/// <para>R11.7. This type is <em>not</em> a compiler primitive. Nothing in the translator
/// mentions it: it is an ordinary user-defined specification type declared through
/// <c>[SpecType]</c>, <c>[SpecCtor]</c> and <c>[SpecOp]</c> (doc/translation.md §11), and
/// it ships here only because a binary tree is common enough to be worth writing once.
/// A user wanting a different model type writes exactly what is below, over an F* module
/// of their own.</para>
///
/// <para>That it can be written this way is the test of the mechanism: it used to be a
/// primitive, with a case in <c>WellKnown.MapType</c>, an <c>IrType</c>, an
/// <c>IrTreeOp</c> node, a <c>TreeOpKind</c> enum, a branch in <c>SpecEmitter</c> and a
/// case of <c>RecursiveShape</c>. All of those are gone and <c>test/binary_tree</c>
/// verifies unchanged.</para>
/// </summary>
[SpecType("Pulse.Lib.CSharp.Tree.tree")]
public readonly struct SpecTree<T>
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecTree<T> is a specification-only construct and has no runtime meaning.");

    /// <summary>The number of interior nodes.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.size")]
    public SpecInt Size => throw Ghost();

    /// <summary>The length of the longest path to a leaf.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.height")]
    public SpecInt Height => throw Ghost();

    /// <summary>R27.16. The left subtree of a branch; a leaf's is a leaf.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.left")]
    public SpecTree<T> Left => throw Ghost();

    /// <summary>R27.16. The right subtree of a branch; a leaf's is a leaf.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.right")]
    public SpecTree<T> Right => throw Ghost();

    /// <summary>R27.16. The root alone, its subtrees dropped; a leaf's is a leaf.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.root_only")]
    public SpecTree<T> RootOnly => throw Ghost();

    /// <summary>True of the empty tree. A discriminator is an ordinary prefix function.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.Leaf?")]
    public bool IsLeaf => throw Ghost();

    public static bool operator ==(SpecTree<T> a, SpecTree<T> b) => throw Ghost();
    public static bool operator !=(SpecTree<T> a, SpecTree<T> b) => throw Ghost();

    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

/// <summary>The constructors and operations of <see cref="SpecTree{T}"/>.</summary>
public static class SpecTree
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecTree is a specification-only construct and has no runtime meaning.");

    /// <summary>The empty tree. What a null reference denotes (R11.3).</summary>
    [SpecCtor("Pulse.Lib.CSharp.Tree.Leaf", Empty = true)]
    public static SpecTree<T> Leaf<T>() => throw Ghost();

    /// <summary>An interior node.</summary>
    [SpecCtor("Pulse.Lib.CSharp.Tree.Branch")]
    public static SpecTree<T> Branch<T>(SpecTree<T> left, T value, SpecTree<T> right) =>
        throw Ghost();

    /// <summary>The in-order traversal, which relates a tree model to a list model.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.elements")]
    public static SpecList<T> Elements<T>(SpecTree<T> tree) => throw Ghost();

    /// <summary>A keyed entry, <c>Pulse.Lib.CSharp.Tree.entry</c>.</summary>
    [SpecCtor("Pulse.Lib.CSharp.Tree.entry")]
    public static SpecKv<T> Entry<T>(SpecInt key, T value) => throw Ghost();

    /// <summary>Whether a map holds <paramref name="key"/>.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.khas")]
    public static bool HasKey<T>(SpecTree<SpecKv<T>> map, SpecInt key) => throw Ghost();

    /// <summary>
    /// What <paramref name="map"/> holds at <paramref name="key"/>, or
    /// <paramref name="fallback"/>. A lookup that returns a value rather than a nullable
    /// reference, because an unconstrained <c>T</c> has no null.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.kget")]
    public static T Get<T>(SpecTree<SpecKv<T>> map, SpecInt key, T fallback) => throw Ghost();

    /// <summary>The keys, in order.</summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.kkeys")]
    public static SpecList<SpecInt> Keys<T>(SpecTree<SpecKv<T>> map) => throw Ghost();

    /// <summary>
    /// Insertion into a map, <c>Pulse.Lib.CSharp.Tree.kinsert</c>. The model of the
    /// destructive operation, in the sense §0 rule 3 means: the library supplies what the
    /// implementation is proved equal to.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.kinsert")]
    public static SpecTree<SpecKv<T>> Insert<T>(SpecTree<SpecKv<T>> map, SpecInt key, T value) =>
        throw Ghost();

    /// <summary>
    /// Binary-search-tree insertion, <c>Pulse.Lib.CSharp.Tree.insert_int</c>. It is the
    /// <em>model</em> of the destructive operation, supplied by the library rather than
    /// written as a user <c>[Spec]</c> function, so that a C# implementation can be proved
    /// equal to it.
    /// </summary>
    [SpecOp("Pulse.Lib.CSharp.Tree.insert_int")]
    public static SpecTree<SpecInt> Insert(SpecTree<SpecInt> tree, SpecInt value) =>
        throw Ghost();
}

/// <summary>
/// A keyed entry, <c>Pulse.Lib.CSharp.Tree.kv</c>. It is what makes a class with an
/// unconstrained type parameter a search tree: C# would order the values with
/// <c>IComparable&lt;T&gt;</c>, and a constrained type parameter is refused (R15.4), so
/// the order lives in an <c>int</c> key carried beside the value.
/// </summary>
[SpecType("Pulse.Lib.CSharp.Tree.kv")]
public readonly struct SpecKv<T>
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecKv<T> is a specification-only construct and has no runtime meaning.");

    /// <summary>The key it is ordered by.</summary>
    [SpecOp("Mkkv?.kv_key")]
    public SpecInt Key => throw Ghost();

    /// <summary>The value it carries.</summary>
    [SpecOp("Mkkv?.kv_value")]
    public T Value => throw Ghost();

    public static bool operator ==(SpecKv<T> a, SpecKv<T> b) => throw Ghost();
    public static bool operator !=(SpecKv<T> a, SpecKv<T> b) => throw Ghost();

    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}
