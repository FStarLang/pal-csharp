using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using PalLang;

// §22. A growable buffer in the style of dotnet/runtime's `List<T>`, verified in place:
// each rule of the collections foundation is exercised by the member that names it.
[assembly: TranslateAnnotatedOnly]

/// <summary>R22.6. A generic `[Spec]` struct as a product model.</summary>
[Spec]
public struct BufferModel<T>
{
    public Seq<T> Items;
    public SpecInt Capacity;
}

/// <summary>R22.2. An enum with no `[SpecType]` is its underlying integer type.</summary>
public enum Argument { Capacity, Index, Value }

public static class Fail
{
    // R22.11. A `[DoesNotReturn]` helper: a call to it is a throw point.
    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    public static void OutOfRange(Argument argument) => throw new ArgumentOutOfRangeException();
}

// R22.5. Not sealed, but nothing derives from it and it declares nothing virtual.
[Invariant("0 <= _size")]
[Invariant("_size <= _items.Length")]
public class Buffer<T>
{
    // R22.7. A `const` is folded where it is read.
    private const int DefaultCapacity = 4;

    private T[] _items;
    private int _size;
    // R22.14. A version stamp wraps rather than carrying an overflow obligation.
    [Wrapping] private int _version;

    // R22.8. A shared empty array is read as a fresh one.
    private static readonly T[] s_empty = new T[0];

    [Refine("Result.Items.Length <= Result.Capacity")]
    [Model]
    private BufferModel<T> Model => new BufferModel<T>
    {
        Items = Pal.Slice(Pal.Contents(_items), 0, _size),
        Capacity = _items.Length,
    };

    [Spec] public Seq<T> Items => Model.Items;
    [Spec] public SpecInt SpecCount => Model.Items.Length;
    [Spec] public SpecInt SpecCapacity => Model.Capacity;

    [Ensures("@this.SpecCount == 0")]
    public Buffer()
    {
        _items = s_empty;
    }

    // R22.9, R22.10, R22.11. A constructor body that branches, allocates `new T[n]` at a
    // type parameter, and throws with the half-built object discarded.
    [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
    [Ensures("capacity >= 0 && @this.SpecCount == 0 && @this.SpecCapacity == capacity")]
    public Buffer(int capacity)
    {
        if (capacity < 0)
            Fail.OutOfRange(Argument.Capacity);

        if (capacity == 0)
            _items = s_empty;
        else
            _items = new T[capacity];
    }

    [Ensures("Result == @this.SpecCount")]
    public int Count => _size;

    // R22.13. Indexer accessors, with contracts on each.
    public T this[int index]
    {
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
        [Ensures("0 <= index && index < @this.SpecCount && Pal.Same(Result, @this.Items[index])")]
        get
        {
            if ((uint)index >= (uint)_size)
                Fail.OutOfRange(Argument.Index);
            return _items[index];
        }

        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
        [Ensures("0 <= index && index < Pal.Old(@this.SpecCount)")]
        [Ensures("@this.Items == Pal.SetAt(Pal.Old(@this.Items), index, value)")]
        set
        {
            if ((uint)index >= (uint)_size)
                Fail.OutOfRange(Argument.Index);
            _items[index] = value;
            _version++;
        }
    }

    // R22.13, R22.17, R22.20. A property with a getter and a setter; the setter's fresh
    // array is declared in a nested block and moved into the field before it closes.
    public int Capacity
    {
        [Ensures("Result == @this.SpecCapacity")]
        get => _items.Length;

        [Throws(typeof(ArgumentOutOfRangeException), "value < @this.SpecCount")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity == value")]
        set
        {
            if (value < _size)
                Fail.OutOfRange(Argument.Value);

            if (value != _items.Length)
            {
                if (value > 0)
                {
                    T[] fresh = new T[value];
                    if (_size > 0)
                        Array.Copy(_items, fresh, _size);
                    _items = fresh;
                }
                else
                {
                    _items = s_empty;
                }
            }
        }
    }

    // R22.16, R22.23. `Add` appends: `Pal.Snoc`, compared extensionally.
    [Requires("@this.SpecCount < int.MaxValue")]
    [Ensures("@this.Items == Pal.Snoc(Pal.Old(@this.Items), item)")]
    public void Add(T item)
    {
        _version++;
        int size = _size;
        if ((uint)size < (uint)_items.Length)
        {
            _size = size + 1;
            _items[size] = item;
        }
        else
        {
            AddWithResize(item);
        }
    }

    // R22.15, R22.19, R22.22. Reads a field, calls a method on its own open receiver,
    // and inherits `Grow`'s need for a default `T`.
    [Requires("@this.SpecCount == @this.SpecCapacity")]
    [Requires("@this.SpecCount < int.MaxValue")]
    [Ensures("@this.Items == Pal.Snoc(Pal.Old(@this.Items), item)")]
    private void AddWithResize(T item)
    {
        Debug.Assert(_size == _items.Length);
        int size = _size;
        Grow(size + 1);
        _size = size + 1;
        _items[size] = item;
    }

    // R22.21. `Capacity = …` is a call of the setter.
    [Requires("@this.SpecCapacity < capacity")]
    [Ensures("@this.Items == Pal.Old(@this.Items)")]
    [Ensures("@this.SpecCapacity >= capacity")]
    private void Grow(int capacity)
    {
        Capacity = NewCapacity(capacity);
    }

    // R22.14 on a method, R22.18. Doubling may wrap; the `(uint)` test catches it.
    [Wrapping]
    [Requires("@this.SpecCapacity < capacity")]
    [Ensures("Result >= capacity")]
    private int NewCapacity(int capacity)
    {
        int next = _items.Length == 0 ? DefaultCapacity : 2 * _items.Length;
        if ((uint)next > Array.MaxLength) next = Array.MaxLength;
        if (next < capacity) next = capacity;
        return next;
    }

    // R22.3. Unannotated: outside the scope, not refused.
    public void Clear() { _size = 0; }
}

/// <summary>
/// R22.15. `Sum` reads `n` and calls `Get()` on the same object: the receiver is folded
/// around the call and reopened after it (once PALCS0597).
/// </summary>
public sealed class Doubler
{
    private int n;

    [Model]
    private SpecInt TheN => n;

    [Spec]
    public SpecInt N => TheN;

    [Ensures("@this.N == a")]
    public Doubler(int a)
    {
        this.n = a;
    }

    [Ensures("Result == @this.N")]
    public int Get()
    {
        return n;
    }

    [Requires("-1073741824 <= @this.N && @this.N <= 1073741823")]
    [Ensures("Result == 2 * @this.N")]
    public int Sum()
    {
        int x = n;
        int y = Get();
        return x + y;
    }
}
