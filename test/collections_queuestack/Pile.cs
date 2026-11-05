using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using PalLang;

// §23. An array-backed stack in the style of dotnet/runtime's `Stack<T>`: each rule of
// the queue/stack family is exercised by the member that names it.
[assembly: TranslateAnnotatedOnly]

[Spec]
public struct PileModel<T>
{
    public Seq<T> Items;
    public SpecInt Capacity;
}

[Invariant("0 <= _size")]
[Invariant("_size <= _array.Length")]
public class Pile<T>
{
    private T[] _array;
    private int _size;

    [Refine("Result.Items.Length <= Result.Capacity")]
    [Model]
    private PileModel<T> Model => new PileModel<T>
    {
        Items = Pal.Slice(Pal.Contents(_array), 0, _size),
        Capacity = _array.Length,
    };

    [Spec] public Seq<T> Items => Model.Items;
    [Spec] public SpecInt SpecCount => Model.Items.Length;
    [Spec] public SpecInt SpecCapacity => Model.Capacity;

    // R23.1. `Array.Empty<T>()` is a fresh empty array.
    [Ensures("@this.SpecCount == 0")]
    public Pile()
    {
        _array = Array.Empty<T>();
    }

    // R23.2. An argument guard is the `if`/`throw` it abbreviates.
    [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
    [Ensures("@this.SpecCount == 0 && @this.SpecCapacity == capacity")]
    public Pile(int capacity)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(capacity);
        _array = new T[capacity];
    }

    [Requires("@this.SpecCount < @this.SpecCapacity")]
    [Ensures("@this.Items == Pal.Snoc(Pal.Old(@this.Items), item)")]
    public void Push(T item)
    {
        _array[_size] = item;
        _size++;
    }

    // R23.5. A bounded `Array.LastIndexOf` agrees with `IndexOf` on finding anything.
    [Ensures("Result == (Pal.IndexOf(@this.Items, item) >= 0)")]
    public bool Contains(T item)
    {
        return _size != 0 && Array.LastIndexOf(_array, item, _size - 1) >= 0;
    }

    // R23.4. `Array.Resize` keeps the prefix that fits.
    [Requires("@this.SpecCount <= capacity")]
    [Ensures("@this.Items == Pal.Old(@this.Items) && @this.SpecCapacity == capacity")]
    public void Resize(int capacity)
    {
        Array.Resize(ref _array, capacity);
    }

    // R23.7. A `[DoesNotReturn]` call on the open receiver closes it once.
    [Throws(typeof(InvalidOperationException), "@this.SpecCount == 0")]
    [Ensures("0 < @this.SpecCount && Pal.Same(Result, @this.Items[@this.SpecCount - 1])")]
    public T Peek()
    {
        if (_size == 0)
        {
            ThrowEmpty();
        }
        return _array[_size - 1];
    }

    [DoesNotReturn]
    [Throws(typeof(InvalidOperationException))]
    [Ensures("false")]
    private void ThrowEmpty() => throw new InvalidOperationException();

    // R23.3: a thrown argument read from a parameter. R23.6: two arrays one of which has a
    // cell are distinct. R23.8: a guard `a || b` keeps both failures. R23.9: `a[--j]`
    // assigns `j`.
    [Requires("@this.SpecCount > 0 || Pal.Contents(array).Length > 0")]
    [Throws(typeof(ArgumentOutOfRangeException), "arrayIndex < 0 || arrayIndex > Pal.Contents(array).Length")]
    [Throws(typeof(ArgumentException), "Pal.Contents(array).Length - arrayIndex < @this.SpecCount")]
    [Ensures("@this.Items == Pal.Old(@this.Items)")]
    [Ensures("0 <= arrayIndex && Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), arrayIndex, arrayIndex + @this.SpecCount, Pal.Reverse(@this.Items))")]
    public void CopyTo(T[] array, int arrayIndex)
    {
        if (arrayIndex < 0 || arrayIndex > array.Length)
        {
            throw new ArgumentOutOfRangeException(nameof(arrayIndex), arrayIndex, "out of range");
        }
        if (array.Length - arrayIndex < _size)
        {
            throw new ArgumentException("too short");
        }

        Debug.Assert(array != _array);
        int srcIndex = 0;
        int dstIndex = arrayIndex + _size;
        while (srcIndex < _size)
        {
            Pal.Invariant(0 <= srcIndex && srcIndex <= _size);
            Pal.Invariant(dstIndex == arrayIndex + _size - srcIndex);
            Pal.Invariant(Pal.Contents(array) ==
                          Pal.Splice(Pal.Old(Pal.Contents(array)), dstIndex, arrayIndex + _size,
                                     Pal.Reverse(Pal.Slice(Pal.Contents(_array), 0, srcIndex))));
            Pal.Decreases(_size - srcIndex);
            array[--dstIndex] = _array[srcIndex++];
        }
    }
}
