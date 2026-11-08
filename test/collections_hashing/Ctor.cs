using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using PalLang;

#pragma warning disable CS0649, CS0414

public static class Halt
{
    [DoesNotReturn]
    [Throws(typeof(InvalidOperationException))]
    [Ensures("false")]
    public static void Concurrent() => throw new InvalidOperationException();
}

// §30. A hash set's constructors and lookups, cut down to the rules they needed.
[Spec]
public struct BagModel<T>
{
    public SpecInt Count;
    public IEqualityComparer<T>? Comparer;
}

[Invariant("0 <= _count")]
public class Bag<T>
{
    private int _count;
    private IEqualityComparer<T>? _comparer;

    [Model]
    private BagModel<T> Model => new BagModel<T> { Count = _count, Comparer = _comparer };

    [Spec] public SpecInt SpecCount => Model.Count;
    [Spec] public IEqualityComparer<T>? SpecComparer => Model.Comparer;

    // R30.19: `(IEqualityComparer<T>?)null` is `None`, and so is the field's default.
    [Ensures("@this.SpecCount == 0 && @this.SpecComparer == null")]
    public Bag() : this((IEqualityComparer<T>?)null) { }

    // R30.21: a nullable comparer against `EqualityComparer<T>.Default`, a type bound to the
    // same F* type. R30.23: what an arm stores in a field survives to the postcondition.
    [Ensures("@this.SpecCount == 0")]
    [Ensures("Pal.Implies(comparer == null, @this.SpecComparer == null)")]
    public Bag(IEqualityComparer<T>? comparer)
    {
        if (comparer is not null && comparer != EqualityComparer<T>.Default)
        {
            _comparer = comparer;
        }
    }

    // R30.24: a chained constructor that throws drops the object it was given.
    [Throws(typeof(ArgumentOutOfRangeException), "count < 0")]
    [Ensures("@this.SpecCount == count")]
    public Bag(int count, IEqualityComparer<T>? comparer) : this(comparer)
    {
        if (count < 0)
        {
            throw new ArgumentOutOfRangeException(nameof(count));
        }
        _count = count;
    }

    // R30.22: the `return` is nested in an `if` with no `else`; what follows is that `else`.
    [Ensures("Result == (@this.SpecCount > 0 && n > 0)")]
    public bool BothPositive(int n)
    {
        if (_count > 0)
        {
            if (n > 0)
            {
                return true;
            }
        }
        return false;
    }

    // R30.26: a call to a bound comparer method writes nothing, so the receiver is only
    // observed, and a caller that holds it read-only (`[Frac]`) may make the call.
    [Ensures("Result == (@this.SpecCount > 0 && EqualityComparer<T>.Default.Equals(a, b))")]
    public bool Agrees(T a, T b) => _count > 0 && EqualityComparer<T>.Default.Equals(a, b);

    [Frac("p")]
    [Ensures("Result == (@this.SpecCount > 0 && EqualityComparer<T>.Default.Equals(a, a))")]
    public bool AgreesWithItself(T a) => Agrees(a, a);

    // R30.27: a read-only loop that may call a `[DoesNotReturn]` helper keeps the receiver
    // as it was, so its measure may still name a field.
    [Throws(typeof(InvalidOperationException), "false")]
    [Ensures("Result == @this.SpecCount")]
    public int CountUp()
    {
        int i = 0;
        while (i < _count)
        {
            Pal.Invariant(0 <= i && i <= _count);
            Pal.Decreases(_count - i);
            i++;
            if (i > _count)
            {
                Halt.Concurrent();
            }
        }
        return i;
    }

    // R30.25: an array parameter compared with `null` in a contract.
    [Requires("array != null")]
    [Ensures("Result == Pal.Contents(array).Length")]
    public static int LengthOf(int[] array)
    {
        if (array == null)
        {
            throw new ArgumentNullException(nameof(array));
        }
        return array.Length;
    }
}
