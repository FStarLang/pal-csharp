using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §15 clients. The operations of a generic singly linked list, written as ordinary C#
/// over <see cref="Cell{T}"/>.
///
/// <para>Every method here is generic in the element type and says nothing about it. That
/// is R14.1's restriction read as a design: with no constraint there is no comparison, no
/// equality and no default value, so what a list library can offer over an unconstrained
/// element is exactly the structural operations — and those are all of them.</para>
/// </summary>
public static class Chains
{
    /// <summary>R10.7's traversal, at a type parameter.</summary>
    [Requires("n.Elements.Length < 2147483647")]
    [Ensures("Result == n.Elements.Length")]
    [Decreases("n.Elements")]
    public static int Size<T>([Frac("p")] Cell<T>? n)
    {
        if (n == null)
        {
            return 0;
        }
        return 1 + Size(n.next);
    }

    /// <summary>R10.6a. Allocation, through the generic constructor.</summary>
    [Ensures("Result.Elements == SpecList.Cons(v, n.Elements)")]
    public static Cell<T> Prepend<T>(T v, [Consumes] Cell<T>? n)
    {
        return new Cell<T>(v, n);
    }

    /// <summary>Whether the chain is empty — the model's shape, read off the null test.</summary>
    [Ensures("Result == n.Elements.IsEmpty")]
    public static bool IsEmpty<T>([Frac("p")] Cell<T>? n)
    {
        if (n == null)
        {
            return true;
        }
        return false;
    }

    /// <summary>
    /// R10.6b. Destructive concatenation: the last <c>next</c> of <c>x</c> is overwritten
    /// with <c>y</c>, and the result owns both.
    /// </summary>
    [Ensures("Result.Elements == SpecList.Append(x.Elements, y.Elements)")]
    [Decreases("x.Elements")]
    public static Cell<T>? Concat<T>([Consumes] Cell<T>? x, [Consumes] Cell<T>? y)
    {
        if (x == null)
        {
            return y;
        }
        x.next = Concat(x.next, y);
        return x;
    }

    /// <summary>
    /// A fresh chain with the same elements. Every operation below is built on this one,
    /// and that is a design decision rather than an economy: an operation that rebuilds
    /// what it returns owns exactly what it allocated, so its argument stays
    /// <c>[Frac]</c>-observed and the caller keeps the list it passed in. The destructive
    /// operations are <see cref="Prepend{T}"/> and <see cref="Concat{T}"/>, and they are
    /// destructive because C# gives them nothing to allocate.
    /// </summary>
    [Ensures("Result.Elements == n.Elements")]
    [Decreases("n.Elements")]
    public static Cell<T>? Copy<T>([Frac("p")] Cell<T>? n)
    {
        if (n == null)
        {
            return null;
        }
        return new Cell<T>(n.value, Copy(n.next));
    }

    /// <summary>
    /// The first <c>k</c> elements. The two guards are the two base cases of
    /// <c>Pulse.Lib.CSharp.List.take</c>, in the order that function tests them.
    /// </summary>
    [Ensures("Result.Elements == SpecList.Take(n.Elements, k)")]
    [Decreases("n.Elements")]
    public static Cell<T>? Take<T>([Frac("p")] Cell<T>? n, int k)
    {
        if (k <= 0)
        {
            return null;
        }
        if (n == null)
        {
            return null;
        }
        return new Cell<T>(n.value, Take(n.next, k - 1));
    }

    /// <summary>Everything but the first <c>k</c> elements.</summary>
    [Ensures("Result.Elements == SpecList.Drop(n.Elements, k)")]
    [Decreases("n.Elements")]
    public static Cell<T>? Drop<T>([Frac("p")] Cell<T>? n, int k)
    {
        if (k <= 0)
        {
            return Copy(n);
        }
        if (n == null)
        {
            return null;
        }
        return Drop(n.next, k - 1);
    }

    /// <summary>
    /// <c>v</c> spliced in as element <c>i</c>. The index guard comes before the null
    /// test, which is what lets the head case hand the whole argument to <see
    /// cref="Copy{T}"/>: it is reached before R10.7 has opened anything.
    /// </summary>
    [Ensures("Result.Elements == SpecList.InsertAt(n.Elements, i, v)")]
    [Decreases("n.Elements")]
    public static Cell<T>? InsertAt<T>([Frac("p")] Cell<T>? n, int i, T v)
    {
        if (i <= 0)
        {
            return new Cell<T>(v, Copy(n));
        }
        if (n == null)
        {
            return new Cell<T>(v, null);
        }
        return new Cell<T>(n.value, InsertAt(n.next, i - 1, v));
    }

    /// <summary>Element <c>i</c> removed; an out-of-range index removes nothing.</summary>
    [Ensures("Result.Elements == SpecList.RemoveAt(n.Elements, i)")]
    [Decreases("n.Elements")]
    public static Cell<T>? RemoveAt<T>([Frac("p")] Cell<T>? n, int i)
    {
        if (i < 0)
        {
            return Copy(n);
        }
        if (n == null)
        {
            return null;
        }
        if (i == 0)
        {
            return Copy(n.next);
        }
        return new Cell<T>(n.value, RemoveAt(n.next, i - 1));
    }

    /// <summary>
    /// The elements in the opposite order. <c>Concat</c> consumes both of its arguments,
    /// and both of the ones handed to it here were allocated by this call — the reversed
    /// tail and a fresh one-element chain — so nothing the caller owns is given away.
    /// </summary>
    [Ensures("Result.Elements == SpecList.Reverse(n.Elements)")]
    [Decreases("n.Elements")]
    public static Cell<T>? Reverse<T>([Frac("p")] Cell<T>? n)
    {
        if (n == null)
        {
            return null;
        }
        return Concat(Reverse(n.next), new Cell<T>(n.value, null));
    }
}
