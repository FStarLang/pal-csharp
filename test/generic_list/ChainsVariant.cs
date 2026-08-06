using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant of <see cref="Chains"/>. Every null test is at the opposite polarity and
/// carries an <c>else</c> instead of falling through, the index guards are written with
/// their operands the other way round, the recursive results are bound to locals before
/// being used, and the type parameter is spelled differently. Same programs, different C#;
/// no emitter change.
/// </summary>
public static class ChainsVariant
{
    [Requires("c.Elements.Length < 2147483647")]
    [Ensures("Result == c.Elements.Length")]
    [Decreases("c.Elements")]
    public static int Count<E>([Frac("q")] Cell<E>? c)
    {
        if (c != null)
        {
            int rest = Count(c.next);
            return rest + 1;
        }
        return 0;
    }

    [Ensures("Result.Elements == SpecList.Cons(e, c.Elements)")]
    public static Cell<E> Push<E>(E e, [Consumes] Cell<E>? c)
    {
        Cell<E> made = new Cell<E>(e, c);
        return made;
    }

    [Ensures("Result == c.Elements.IsEmpty")]
    public static bool Empty<E>([Frac("q")] Cell<E>? c)
    {
        if (c != null)
        {
            return false;
        }
        return true;
    }

    [Ensures("Result.Elements == SpecList.Append(a.Elements, b.Elements)")]
    [Decreases("a.Elements")]
    public static Cell<E>? Join<E>([Consumes] Cell<E>? a, [Consumes] Cell<E>? b)
    {
        if (a != null)
        {
            a.next = Join(a.next, b);
            return a;
        }
        return b;
    }

    [Ensures("Result.Elements == c.Elements")]
    [Decreases("c.Elements")]
    public static Cell<E>? Clone<E>([Frac("q")] Cell<E>? c)
    {
        if (c != null)
        {
            Cell<E>? tail = Clone(c.next);
            return new Cell<E>(c.value, tail);
        }
        return null;
    }

    [Ensures("Result.Elements == SpecList.Take(c.Elements, m)")]
    [Decreases("c.Elements")]
    public static Cell<E>? Prefix<E>([Frac("q")] Cell<E>? c, int m)
    {
        if (0 < m)
        {
            if (c != null)
            {
                return new Cell<E>(c.value, Prefix(c.next, m - 1));
            }
            return null;
        }
        return null;
    }

    [Ensures("Result.Elements == SpecList.Drop(c.Elements, m)")]
    [Decreases("c.Elements")]
    public static Cell<E>? Suffix<E>([Frac("q")] Cell<E>? c, int m)
    {
        if (0 < m)
        {
            if (c != null)
            {
                return Suffix(c.next, m - 1);
            }
            return null;
        }
        return Clone(c);
    }

    [Ensures("Result.Elements == SpecList.InsertAt(c.Elements, at, e)")]
    [Decreases("c.Elements")]
    public static Cell<E>? Splice<E>([Frac("q")] Cell<E>? c, int at, E e)
    {
        if (0 < at)
        {
            if (c != null)
            {
                Cell<E>? tail = Splice(c.next, at - 1, e);
                return new Cell<E>(c.value, tail);
            }
            return new Cell<E>(e, null);
        }
        return new Cell<E>(e, Clone(c));
    }

    [Ensures("Result.Elements == SpecList.RemoveAt(c.Elements, at)")]
    [Decreases("c.Elements")]
    public static Cell<E>? Excise<E>([Frac("q")] Cell<E>? c, int at)
    {
        if (at < 0)
        {
            return Clone(c);
        }
        if (c != null)
        {
            if (0 < at)
            {
                Cell<E>? tail = Excise(c.next, at - 1);
                return new Cell<E>(c.value, tail);
            }
            return Clone(c.next);
        }
        return null;
    }

    [Ensures("Result.Elements == SpecList.Reverse(c.Elements)")]
    [Decreases("c.Elements")]
    public static Cell<E>? Flip<E>([Frac("q")] Cell<E>? c)
    {
        if (c != null)
        {
            Cell<E>? front = Flip(c.next);
            Cell<E> last = new Cell<E>(c.value, null);
            return Join(front, last);
        }
        return null;
    }
}
