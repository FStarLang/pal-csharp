using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
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
    public void Reset() { _size = 0; }

    // R22.25, R22.26. Clearing a range at a type parameter, guarded by the JIT constant.
    [Ensures("@this.SpecCount == 0")]
    public void Clear()
    {
        _version++;
        if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
        {
            int size = _size;
            _size = 0;
            if (size > 0)
                Array.Clear(_items, 0, size);
        }
        else
        {
            _size = 0;
        }
    }

    // R22.25. An overlapping copy down, then a defaulted cell.
    [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
    [Ensures("0 <= index && index < Pal.Old(@this.SpecCount)")]
    [Ensures("@this.Items == Pal.Concat(Pal.Slice(Pal.Old(@this.Items), 0, index), " +
             "Pal.Slice(Pal.Old(@this.Items), index + 1, Pal.Old(@this.SpecCount)))")]
    public void RemoveAt(int index)
    {
        if ((uint)index >= (uint)_size)
            Fail.OutOfRange(Argument.Index);
        _size--;
        if (index < _size)
            Array.Copy(_items, index + 1, _items, index, _size - index);
        if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
            _items[_size] = default!;
        _version++;
    }

    // R22.25. An overlapping copy up, after growing if full.
    [Requires("@this.SpecCount < int.MaxValue")]
    [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index > @this.SpecCount")]
    [Ensures("0 <= index && index <= Pal.Old(@this.SpecCount)")]
    [Ensures("@this.Items == Pal.Concat(Pal.Snoc(Pal.Slice(Pal.Old(@this.Items), 0, index), item), " +
             "Pal.Slice(Pal.Old(@this.Items), index, Pal.Old(@this.SpecCount)))")]
    public void Insert(int index, T item)
    {
        if ((uint)index > (uint)_size)
            Fail.OutOfRange(Argument.Index);
        if (_size == _items.Length) Grow(_size + 1);
        if (index < _size)
            Array.Copy(_items, index, _items, index + 1, _size - index);
        _items[index] = item;
        _size++;
        _version++;
    }

    // R22.25. Searches by the default equality.
    [Ensures("Result == Pal.IndexOf(@this.Items, item)")]
    public int IndexOf(T item) => Array.IndexOf(_items, item, 0, _size);

    [Ensures("Result == Pal.LastIndexOf(@this.Items, item)")]
    public int LastIndexOf(T item)
    {
        if (_size == 0) return -1;
        return Array.LastIndexOf(_items, item, _size - 1, _size);
    }

    [Ensures("Result == (Pal.IndexOf(@this.Items, item) >= 0)")]
    public bool Contains(T item) => _size != 0 && IndexOf(item) >= 0;

    [Ensures("@this.Items == Pal.Reverse(Pal.Old(@this.Items))")]
    public void Reverse()
    {
        if (_size > 1)
            Array.Reverse(_items, 0, _size);
        _version++;
    }

    // R22.25. A copy into another array.
    [Requires("arrayIndex >= 0 && arrayIndex + @this.SpecCount <= Pal.Contents(array).Length")]
    [Ensures("@this.Items == Pal.Old(@this.Items)")]
    [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
    [Ensures("Pal.Slice(Pal.Contents(array), arrayIndex, arrayIndex + @this.SpecCount) == @this.Items")]
    public void CopyTo(T[] array, int arrayIndex)
    {
        Array.Copy(_items, 0, array, arrayIndex, _size);
    }

    // R22.28. A returned array is owned by the caller.
    [Ensures("Pal.Contents(Result) == @this.Items")]
    public T[] ToArray()
    {
        if (_size == 0) return s_empty;
        T[] array = new T[_size];
        Array.Copy(_items, array, _size);
        return array;
    }

    // R22.11/R22.12. Each throwing arm ends in `unreachable ()`, the last in tail position.
    [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
    [Ensures("0 <= index && index < @this.SpecCount && Pal.Same(Result, @this.Items[index])")]
    public T At(int index)
    {
        if (index < 0) Fail.OutOfRange(Argument.Index);
        if (index < _size) return _items[index];
        Fail.OutOfRange(Argument.Index);
        return default!;
    }

    // R22.27. `checked` arithmetic carries the no-overflow obligation.
    [Requires("@this.SpecCount < int.MaxValue")]
    [Ensures("Result == @this.SpecCount + 1")]
    public int NextSize() => checked(_size + 1);
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
