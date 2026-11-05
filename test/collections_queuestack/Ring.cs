using System;
using PalLang;

// §23. A circular buffer in the style of dotnet/runtime's `Queue<T>`: R23.10–R23.14.

[Spec]
public struct RingModel<T>
{
    public Seq<T> Items;
    public SpecInt Capacity;
    public Seq<T> Store;
    public SpecInt Head;
}

[Invariant("0 <= _size")]
[Invariant("_size <= _array.Length")]
[Invariant("0 <= _head")]
[Invariant("_head < _array.Length || _head == 0")]
[Invariant("_tail == (_head + _size < _array.Length ? _head + _size : _head + _size - _array.Length)")]
public class RingBuffer<T>
{
    private T[] _array;
    private int _head;
    private int _tail;
    private int _size;

    // R23.10. The live elements are the store read from the head, wrapping once.
    [Refine("Result.Items.Length <= Result.Capacity && Result.Store.Length == Result.Capacity")]
    [Model]
    private RingModel<T> Model => new RingModel<T>
    {
        Items = Pal.Ring(Pal.Contents(_array), _head, _size),
        Capacity = _array.Length,
        Store = Pal.Contents(_array),
        Head = _head,
    };

    [Spec] public Seq<T> Items => Model.Items;
    [Spec] public SpecInt SpecCount => Model.Items.Length;
    [Spec] public SpecInt SpecCapacity => Model.Capacity;

    // R23.13. `[]` is a fresh empty array.
    [Ensures("@this.SpecCount == 0")]
    public RingBuffer()
    {
        _array = [];
    }

    [Requires("0 <= index && index < @this.SpecCapacity")]
    [Ensures("index == (Pal.Old(index) + 1 == @this.SpecCapacity ? 0 : Pal.Old(index) + 1)")]
    private void MoveNext(ref int index)
    {
        int tmp = index + 1;
        if (tmp == _array.Length)
        {
            tmp = 0;
        }
        index = tmp;
    }

    // R23.11. `_tail` is passed by `ref` through a local copy.
    [Requires("@this.SpecCount < @this.SpecCapacity")]
    [Ensures("@this.Items == Pal.Snoc(Pal.Old(@this.Items), item)")]
    public void Enqueue(T item)
    {
        _array[_tail] = item;
        MoveNext(ref _tail);
        _size++;
    }

    // R23.14. The remaining items are compared pointwise with the old ones.
    [Requires("0 < @this.SpecCount")]
    [Ensures("Pal.Same(Result, Pal.Old(@this.Items)[0])")]
    [Ensures("@this.Items == Pal.Slice(Pal.Old(@this.Items), 1, Pal.Old(@this.SpecCount))")]
    public T Dequeue()
    {
        T removed = _array[_head];
        MoveNext(ref _head);
        _size--;
        return removed;
    }

    // R23.12. `Math.Min` is a conditional.
    [Ensures("Result == (@this.SpecCount <= n ? @this.SpecCount : n)")]
    public int Take(int n)
    {
        return Math.Min(_size, n);
    }
}
