using System;
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Spec]
public struct StoreModel<T>
{
    public Seq<T> Values;
    public SpecInt Revision;
}

[Invariant("_items.Length == 1 && _revision >= 0")]
public sealed class Store<T> : IEnumerable<T>
{
    private T[] _items;
    private int _revision;
    [Model]
    [Refine("Result.Values.Length == 1 && Result.Revision >= 0")]
    private StoreModel<T> Model => new StoreModel<T> { Values = Pal.Contents(_items), Revision = _revision };
    [Spec, EnumerationModel] public Seq<T> Elements => Model.Values;
    [Spec] public SpecInt Revision => Model.Revision;

    [Ensures("@this.Elements.Length == 1 && Pal.Same(@this.Elements[0], value) && @this.Revision == 7")]
    public Store(T value) { _items = new T[1]; _items[0] = value; _revision = 7; }

    [Requires("@this.Revision < int.MaxValue")]
    [Ensures("@this.Revision == Pal.Old(@this.Revision) + 1")]
    public void Invalidate() { _revision++; }

    [Ensures("Result == @this.Elements.Length")]
    public int Count => _items.Length;

    [Frac("p")]
    [Requires("index >= 0 && index + @this.Elements.Length <= Pal.Contents(array).Length")]
    [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Elements.Length, @this.Elements)")]
    public void CopyTo(T[] array, int index) => Array.Copy(_items, 0, array, index, _items.Length);

    [Ensures("ReferenceEquals(Result._owner, @this) && Result._index == 0 && Result._revision == @this.Revision")]
    public Enumerator GetEnumerator() => new Enumerator(this, 0);

    [Ensures("Pal.Exists((Store<T>.Enumerator e) => Pal.Boxes(Result, e) && ReferenceEquals(e._owner, @this) && e._index == 0)")]
    IEnumerator<T> IEnumerable<T>.GetEnumerator() => GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<T>)this).GetEnumerator();

    // A proof traversal, not an alternative enumeration implementation. The
    // compiler checks its exact protocol shape and nominal slot correspondence.
    [EnumerationProtocol]
    [Frac("p")]
    [Ensures("Pal.Yielded<T>().Length == 1 && Pal.Same(Pal.Yielded<T>()[0], @this.Elements[0])")]
    public IEnumerable<T> Trace()
    {
        Enumerator e = GetEnumerator();
        while (e.MoveNext())
        {
            Pal.Invariant(e.Ready);
            Pal.Invariant(Pal.Yielded<T>().Length == e.Index);
            Pal.Invariant(Pal.Implies(e.Index == 1, Pal.Same(Pal.Yielded<T>()[0], this.Elements[0])));
            Pal.Decreases(1 - e.Index);
            yield return e.Current;
        }
        e.Dispose();
    }

    // The CLR allocates one box. Its nonescaping mutable state is represented by
    // one held borrowing struct; Dispose is an actual verified member call.
    [Frac("p")]
    [Ensures("Result && @this.Revision == Pal.Old(@this.Revision)")]
    public bool Partial(bool advance)
    {
        IEnumerator<T> e = ((IEnumerable<T>)this).GetEnumerator();
        bool result = true;
        if (advance)
        {
            bool more = e.MoveNext();
            T value = e.Current;
            Pal.Assert(Pal.Same(value, this.Elements[0]));
            result = more;
        }
        e.Dispose();
        return result;
    }

    [EnumerationState(nameof(Ready), nameof(Remaining), nameof(Value), nameof(Valid))]
    public struct Enumerator : IEnumerator<T>
    {
        private readonly Store<T> _owner;
        private int _index;
        private T? _current;
        private readonly int _revision;
        [Spec] public bool Ready => 0 <= _index && _index <= 1 && _revision == _owner.Revision;
        [Spec] public SpecInt Index => _index;
        [Spec] public Seq<T> Remaining => Pal.Slice(_owner.Elements, _index, 1);
        [Spec] public T Value => _current!;
        [Spec] public bool Valid => _index == 1;

        [Requires("0 <= start && start <= 1")]
        [Ensures("ReferenceEquals(@this._owner, owner) && @this._index == start && @this._revision == owner.Revision")]
        internal Enumerator(Store<T> owner, int start) { _owner = owner; _index = start; _current = default; _revision = owner._revision; }

        [Requires("0 <= @this._index && @this._index <= 1")]
        [Throws(typeof(InvalidOperationException), "@this._revision != @this._owner.Revision")]
        [Ensures("@this.Ready && Result == (Pal.Old(@this._index) == 0)")]
        [Ensures("@this._index == 1")]
        [Ensures("Pal.Implies(Result, Pal.Same(@this._current, @this._owner.Elements[0]))")]
        public bool MoveNext()
        {
            if (_revision != _owner._revision) throw new InvalidOperationException();
            if (_index == 0) { _current = _owner._items[0]; _index = 1; return true; }
            return false;
        }
        [Ensures("Pal.Same(Result, @this._current)")]
        public T Current => _current!;
        [Requires("@this.Ready && @this.Valid")]
        [Ensures("Pal.Boxes(Result, @this._current)")]
        object? IEnumerator.Current => Current;
        [Ensures("@this._index == 0")]
        void IEnumerator.Reset() { _index = 0; }
        [Ensures("true")]
        public void Dispose() { }
    }
}

public static class ProtocolClient
{
    [Requires("Pal.Contents(input).Length == 1")]
    [Ensures("Result == (input is Store<int>)")]
    public static bool LoopCast(IEnumerable<int> input, bool early)
    {
        var candidate = input as Store<int>;
        if (candidate != null && candidate.Count == 1)
        {
            int remaining = candidate.Count;
            while (remaining > 0)
            {
                Pal.Invariant(0 <= remaining && remaining <= 1 &&
                    Pal.Implies(Pal.Returned(), Pal.ReturnValue<bool>()));
                Pal.Decreases(remaining);
                if (early) return true;
                remaining--;
            }
            return candidate.Count == 1;
        }
        return false;
    }

    [Ensures("Result")]
    public static bool LoopClient(bool early)
    {
        Store<int> source = new Store<int>(23);
        bool result = LoopCast(source, early);
        Pal.Assert(source.Revision == 7 && source.Elements[0] == 23);
        return result;
    }

    [Ensures("Result")]
    public static bool Stale()
    {
        Store<int> source = new Store<int>(23);
        Store<int>.Enumerator e = source.GetEnumerator();
        source.Invalidate();
        int caught = 0;
        try { Pal.Invariant(Pal.Implies(!Pal.Raised(), caught == 1)); e.MoveNext(); }
        catch (InvalidOperationException) { caught = 1; }
        return caught == 1;
    }

    [Requires("Pal.Contents(input).Length == 1")]
    [Ensures("Result")]
    public static bool SnapshotOnly(IEnumerable<int> input)
    {
        using IEnumerator<int> e = input.GetEnumerator();
        return e.MoveNext();
    }

    [Requires("Pal.Contents(input).Length == 1")]
    [Ensures("Result")]
    public static bool GuardFalse(IEnumerable<int> input)
    {
        var candidate = input as Store<int>;
        if (candidate != null && candidate.Count == 0) return false;
        return SnapshotOnly(input);
    }

    [Requires("Pal.Contents(input).Length == 1")]
    [Ensures("Result == (input is Store<int>)")]
    public static bool Forward(IEnumerable<int> input)
    {
        if (input is Store<int> candidate) { int count = candidate.Count; Pal.Assert(count == 1); }
        bool snapshot = SnapshotOnly(input);
        Pal.Assert(snapshot);
        bool guard = GuardFalse(input);
        Pal.Assert(guard);
        // The first call returns the same source loan. The second forwards that
        // descriptor unchanged at a differently named formal parameter.
        return Test(input);
    }

    [Ensures("Result")]
    public static bool ForwardClient()
    {
        Store<int> source = new Store<int>(23);
        bool answer = Forward(source);
        Pal.Assert(source.Revision == 7 && source.Elements[0] == 23);
        return answer;
    }

    [Requires("Pal.Contents(other).Length == 1")]
    [Ensures("Result == (other is Store<int>)")]
    public static bool Test(IEnumerable<int> other)
    {
        var candidate = other as Store<int>;
        if (candidate != null && candidate.Count == 1) return true;
        using IEnumerator<int> e = other.GetEnumerator();
        return !e.MoveNext();
    }

    [Ensures("Result")]
    public static bool Successful()
    {
        Store<int> source = new Store<int>(23);
        bool partial = source.Partial(true);
        bool empty = source.Partial(false);
        bool result = Test(source);
        Pal.Assert(source.Revision == 7 && source.Elements[0] == 23);
        return partial && empty && result;
    }

    [Requires("Pal.Contents(other).Length == 1")]
    [Ensures("Result == (other is Other)")]
    public static bool TestMiss(IEnumerable<int> other)
    {
        if (other is Other candidate) return candidate.Count == 1;
        using IEnumerator<int> e = other.GetEnumerator();
        return !e.MoveNext();
    }

    [Requires("Pal.Contents(other).Length == 1")]
    [Ensures("Result")]
    public static bool Terminal(IEnumerable<int> other)
    {
        if (other is Store<int> candidate) { int count = candidate.Count; Pal.Assert(count == 1); }
        using IEnumerator<int> e = other.GetEnumerator();
        bool more = e.MoveNext();
        bool end = e.MoveNext();
        bool again = e.MoveNext();
        return more && !end && !again;
    }

    [Ensures("!Result")]
    public static bool Failed()
    {
        Store<int> source = new Store<int>(23);
        bool result = TestMiss(source);
        bool terminal = Terminal(source);
        Pal.Assert(terminal);
        Pal.Assert(source.Revision == 7 && source.Elements[0] == 23);
        return result;
    }

    [Ensures("Result")]
    public static bool Generic<T>(T value)
    {
        Store<T> source = new Store<T>(value);
        bool result = source.Partial(true);
        Pal.Assert(source.Revision == 7 && Pal.Same(source.Elements[0], value));
        return result;
    }

    [Ensures("Result")]
    public static bool StaticBox()
    {
        Store<int> source = new Store<int>(23);
        IEnumerator<int> e = ((IEnumerable<int>)source).GetEnumerator();
        bool more = e.MoveNext();
        int value = e.Current;
        e.Dispose();
        Pal.Assert(source.Revision == 7 && source.Elements[0] == 23);
        return more && value == 23;
    }

    [Ensures("Result")]
    public static bool StaticStruct()
    {
        Store<int> source = new Store<int>(23);
        Store<int>.Enumerator e = source.GetEnumerator();
        bool more = e.MoveNext();
        int value = e.Current;
        e.Dispose();
        Pal.Assert(source.Revision == 7 && source.Elements[0] == 23);
        return more && value == 23;
    }
}

[Invariant("_items.Length == 1")]
public sealed class Other : IEnumerable<int>
{
    private int[] _items;
    [Model, Refine("Result.Length == 1")]
    private Seq<int> Model => Pal.Contents(_items);
    [Ensures("Result == 1")]
    public int Count => _items.Length;
    [Ensures("true")]
    public Other() { _items = new int[1]; }
    public IEnumerator<int> GetEnumerator() { yield return _items[0]; }
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
