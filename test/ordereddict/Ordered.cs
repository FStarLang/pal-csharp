using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using PalLang;
using static System.Collections.ThrowHelper;

// §33. The shapes of dotnet/runtime's `OrderedDictionary<TKey,TValue>`, each rule exercised by
// the member that names it.
[assembly: TranslateAnnotatedOnly]
[assembly: SpecBinding("P:System.IntPtr.Size", "Pulse.Lib.CSharp.Platform.intptr_size")]
[assembly: SpecBinding("T:System.Collections.Generic.IEqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]
[assembly: SpecBinding("M:System.Collections.Generic.IEqualityComparer`1.Equals(`0,`0)", "Pulse.Lib.CSharp.Equality.equals")]
[assembly: SpecBinding("T:System.Collections.Generic.EqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]
[assembly: SpecBinding("P:System.Collections.Generic.EqualityComparer`1.Default", "Pulse.Lib.CSharp.Equality.default_comparer")]

public static class SlotSpecs
{
    [Spec]
    public static bool Nonempty(Seq<OrderedTable.Slot> xs) => xs.Length > 0;
}

[Spec]
public struct OrderedTableModel
{
    public Seq<OrderedTable.Slot> Slots;
    public bool NoBuckets;
}

[Invariant("_slots != null")]
[Invariant("_wide == (IntPtr.Size == 8)")]
public class OrderedTable
{
    public struct Slot
    {
        public int Key;
        public int Next;
    }

    private Slot[] _slots;
    private int[]? _buckets;
    private bool _wide;

    [Model]
    private OrderedTableModel Model => new OrderedTableModel { Slots = Pal.Contents(_slots), NoBuckets = _buckets == null };

    [Spec] internal bool SpecNoBuckets => Model.NoBuckets;
    [Spec] internal Seq<Slot> SpecSlots => Model.Slots;

    // R33.4. A bound machine-integer member (`IntPtr.Size`) in code and in an invariant.
    public OrderedTable()
    {
        _slots = new Slot[4];
        _buckets = null;
        _wide = IntPtr.Size == 8;
    }

    // R33.1.
    [Requires("n >= 0")]
    [Ensures("Result == n")]
    private static int Guarded(int n)
    {
        ThrowIfNegative(n);
        return n;
    }

    // R33.6. `is null` on an array is a real test, not `false`.
    [Ensures("Result == @this.SpecNoBuckets")]
    private bool NoBuckets() => _buckets is null;

    [Ensures("Result == !@this.SpecNoBuckets")]
    private bool HasBuckets() => _buckets is not null;

    // R33.3. A `ref`-returning method with `Debug.Assert`s and a two-way `return ref`.
    private ref Slot SlotAt(int i, bool first)
    {
        Debug.Assert(i >= 0);
        if (first) return ref _slots[0];
        else return ref _slots[i];
    }

    [Requires("0 <= i && i < @this.SpecSlots.Length")]
    [Ensures("Result == @this.SpecSlots[i].Key")]
    private int KeyAt(int i) => SlotAt(i, false).Key;

    // R33.2. `r` is declared between the jump and its label.
    [Ensures("Result >= 0")]
    private static int Clamp(int n)
    {
        if (n < 0) goto Negative;
        int r = n;
        return r;

    Negative:
        r = 0;
        return r;
    }

    // R33.2 and R33.5. A chain walk through a rebound `ref` local, leaving by forward
    // `goto`s; the label after the `[DoesNotReturn]` call is reached only by jumps.
    [Requires("0 <= start")]
    [Ensures("-1 <= Result && Result < @this.SpecSlots.Length")]
    [Throws(typeof(InvalidOperationException))]
    private int Find(int start, int key)
    {
        ref Slot slot = ref Unsafe.NullRef<Slot>();
        Slot[] slots = _slots;
        int i = start;
        int steps = 0;
        while (steps < slots.Length)
        {
            Pal.Invariant(Pal.Returned() || 0 <= i);
            Pal.Invariant(Pal.Implies(Pal.Returned(), -1 <= Pal.Result<int>() && Pal.Result<int>() < slots.Length));
            Pal.Invariant(slots == _slots);
            Pal.Invariant(steps <= slots.Length);
            Pal.Decreases(slots.Length - steps);
            if ((uint)i >= (uint)slots.Length)
            {
                goto NotFound;
            }
            slot = ref slots[i];
            if (slot.Key == key)
            {
                goto Found;
            }
            i = slot.Next;
            if (i < 0) goto NotFound;
            steps++;
        }
        goto Cycle;

    NotFound:
        return -1;

    Cycle:
        System.Collections.ThrowHelper.ThrowCycle();

    Found:
        return i;
    }

    // R33.8. `a?.Length ?? d` on an array.
    [Ensures("Pal.Implies(@this.SpecNoBuckets, Result == 0) && Result >= 0")]
    public int BucketCount => _buckets?.Length ?? 0;

    [Ensures("Result == 3")]
    private static int Fill(int k, out int v, ref int a, ref int b)
    {
        v = k;
        a = 1;
        b = 2;
        Pal.Assert(a == 1);
        return 3;
    }

    // R33.7. An `out _` discard, and one local passed twice by `ref` to parameters the callee
    // only assigns.
    [Ensures("Result == 3")]
    public static int Discard(int k)
    {
        int _ = 0;
        return Fill(k, out int _, ref _, ref _);
    }
    [Ensures("Result == (n >= 0) && h == n / 2")]
    private static bool Half(int n, out int h)
    {
        h = n / 2;
        return n >= 0;
    }

    // R33.9. An `out` variable declared in an `if`'s condition, read after the `if`.
    [Ensures("n >= 0 ? Result == n / 2 : Result == -1")]
    public static int HalfOr(int n)
    {
        if (!Half(n, out int h))
        {
            return -1;
        }
        return h;
    }

    // R33.10. Writing an element through a local copy of a field's array writes the field;
    // a local that only ever holds new arrays does not.
    [Requires("0 < @this.SpecSlots.Length")]
    [Ensures("@this.SpecSlots.Length == Pal.Old(@this.SpecSlots).Length && @this.SpecSlots[0].Key == k")]
    public void SetFirstKey(int k)
    {
        Slot[] slots = _slots;
        Slot s = slots[0];
        s.Key = k;
        slots[0] = s;
    }

    [Ensures("Result == k")]
    public static int Scratch(int k)
    {
        int[] a = new int[1];
        a[0] = k;
        return a[0];
    }

    // R33.11. `??=` on a parameter: a comparer, an `int?`, and a bound comparer type.
    [Ensures("Result == (c ?? System.Collections.Generic.Comparer<int>.Default)")]
    public static System.Collections.Generic.IComparer<int> OrderOrDefault(System.Collections.Generic.IComparer<int>? c)
    {
        c ??= System.Collections.Generic.Comparer<int>.Default;
        return c;
    }

    [Ensures("n != null ? Result == n : Result == 0")]
    public static int OrZero(int? n)
    {
        n ??= 0;
        return n.Value;
    }

    // R33.14. Reading through a comparer and handing `Pal.Contents(_slots)` to a `[Spec]` is
    // read-only, so `Twice` knows the slots are still there; a loop that raises inside is
    // read-only too and measures by its field's length; and `Debug.Assert(a != _slots)`
    // holds of a whole array and a read-only field.
    [Requires("0 < @this.SpecSlots.Length")]
    [Ensures("Pal.Implies(Result, @this.SpecSlots[0].Key == x)")]
    private bool Same(System.Collections.Generic.IEqualityComparer<int> c, int x, int y)
    {
        Pal.Assert(SlotSpecs.Nonempty(Pal.Contents(_slots)));
        return c.Equals(x, y) && _slots[0].Key == x;
    }

    [Requires("0 < @this.SpecSlots.Length")]
    [Ensures("Result == @this.SpecSlots[0].Key")]
    public int Twice(System.Collections.Generic.IEqualityComparer<int> c, int x)
    {
        bool _ = Same(c, x, x);
        return KeyAt(0);
    }

    [Ensures("Result >= 0")]
    [Throws(typeof(InvalidOperationException))]
    private int Walk()
    {
        Slot[] slots = _slots;
        int i = 0;
        while (i < slots.Length)
        {
            Pal.Invariant(0 <= i && i <= slots.Length);
            Pal.Decreases(slots.Length - i);
            if (slots[i].Next < -1)
                System.Collections.ThrowHelper.ThrowCycle();
            i++;
        }
        return i;
    }

    [Requires("Pal.Contents(a).Length > 0")]
    private void Apart(Slot[] a)
    {
        Debug.Assert(a != _slots);
    }

    // A write through a `ref` local into the field's array is a write of the field.
    [Requires("0 < @this.SpecSlots.Length")]
    [Ensures("@this.SpecSlots.Length == Pal.Old(@this.SpecSlots).Length && @this.SpecSlots[0].Key == k")]
    public void SetFirstKeyRef(int k)
    {
        ref Slot s = ref _slots[0];
        s.Key = k;
    }

    [Ensures("Result")]
    public static bool SelfEqual<T>(System.Collections.Generic.IEqualityComparer<T>? c, T x)
    {
        c ??= System.Collections.Generic.EqualityComparer<T>.Default;
        return c != null;
    }
}

// R33.12. Explicit indexer accessors and an explicit setter, two of them sharing `get_Item`.
// R33.13. An expression-bodied constructor and an expression-bodied indexer.
public interface IRow { bool this[int i] { get; set; } }
public interface IRowReadOnly { bool this[int i] { get; } }

public sealed class Row : IRow, IRowReadOnly
{
    private bool _value;

    [Model]
    private bool Model => _value;

    [Spec] internal bool SpecValue => Model;

    [Ensures("@this.SpecValue == v")]
    public Row(bool v) => _value = v;

    bool IRow.this[int i]
    {
        [Ensures("Result == @this.SpecValue")]
        get => _value;
        [Throws(typeof(NotSupportedException))]
        [Ensures("false")]
        set => throw new NotSupportedException();
    }

    [Ensures("Result == @this.SpecValue")]
    bool IRowReadOnly.this[int i] => _value;
}

// R33.15. An `[Open]` helper of a class that owns arrays.
[Spec]
public struct CellsModel
{
    public Seq<int> Items;
    public SpecInt Count;
}

[Invariant("0 <= _n && _n <= _a.Length")]
public class Cells
{
    private int[] _a;
    private int _n;

    [Model]
    private CellsModel Model => new CellsModel { Items = Pal.Contents(_a), Count = _n };

    [Spec] internal Seq<int> SpecItems => Model.Items;
    [Spec] internal SpecInt SpecCount => Model.Count;

    [Ensures("@this.SpecItems.Length == 4 && @this.SpecCount == 0")]
    public Cells()
    {
        _a = new int[4];
        _n = 0;
    }

    [Open]
    [Requires("0 <= i && i < Pal.Contents(@this._a).Length")]
    [Ensures("Pal.Contents(@this._a) == Pal.SetAt(Pal.Old(Pal.Contents(@this._a)), i, v)")]
    [Ensures("@this._n == Pal.Old(@this._n)")]
    private void Put(int i, int v)
    {
        _a[i] = v;
    }

    [Requires("0 < @this.SpecItems.Length")]
    [Ensures("@this.SpecItems.Length == Pal.Old(@this.SpecItems).Length && @this.SpecItems[0] == v")]
    public void PutFirst(int v)
    {
        Put(0, v);
    }

    [Open]
    [Requires("0 <= @this._n && @this._n <= Pal.Contents(@this._a).Length")]
    [Ensures("Pal.Contents(@this._a).Length == Pal.Old(Pal.Contents(@this._a)).Length")]
    [Ensures("@this._n == Pal.Old(@this._n)")]
    [Ensures("Pal.Forall((int j) => Pal.Implies(0 <= j && j < @this._n, Pal.Contents(@this._a)[j] == v))")]
    private void FillOpen(int v)
    {
        for (int k = 0; k < _n; k++)
        {
            Pal.Invariant(0 <= k && k <= _n);
            Pal.Invariant(Pal.Contents(_a).Length == Pal.Old(Pal.Contents(this._a)).Length && _n == Pal.Old(this._n));
            Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < k, Pal.Contents(_a)[j] == v)));
            _a[k] = v;
        }
    }

    [Ensures("@this.SpecItems.Length == Pal.Old(@this.SpecItems).Length")]
    public void Fill(int v)
    {
        FillOpen(v);
    }

    // R33.27. A window of the receiver's array, left borrowed when a loop returns.
    [Ensures("-1 <= Result && Result < @this.SpecCount")]
    [Ensures("Pal.Implies(Result >= 0, Result < @this.SpecItems.Length && @this.SpecItems[Result] == x)")]
    public int Find(int x)
    {
        ReadOnlySpan<int> s = _a.AsSpan(0, _n);
        for (int i = 0; i < s.Length; i++)
        {
            Pal.Invariant(0 <= i && i <= s.Length);
            Pal.Invariant(Pal.Implies(Pal.Returned(), i < s.Length && Pal.ReturnValue<int>() == i && Pal.Contents(s)[i] == x));
            if (s[i] == x)
            {
                return i;
            }
        }
        return -1;
    }

    // R33.28. The fields of a fresh object of the class, written.
    [Ensures("Result.SpecCount == 1 && 0 < Result.SpecItems.Length && Result.SpecItems[0] == v")]
    public static Cells One(int v)
    {
        Cells c = new Cells();
        c._a[0] = v;
        c._n = 1;
        return c;
    }
}

public enum Mode { Keep, Fail, Bump }

[Spec]
public struct LedgerModel
{
    public Seq<OrderedTable.Slot> Slots;
    public SpecInt Count;
    public SpecInt Tag;
}

[Invariant("0 <= _n && _n <= _slots.Length")]
public class Ledger
{

    private OrderedTable.Slot[] _slots;
    private int _n;
    private int _tag;

    [Model]
    private LedgerModel Model => new LedgerModel { Slots = Pal.Contents(_slots), Count = _n, Tag = _tag };

    [Spec] internal Seq<OrderedTable.Slot> SpecSlots => Model.Slots;
    [Spec] internal SpecInt SpecCount => Model.Count;
    [Spec] internal SpecInt SpecTag => Model.Tag;

    public Ledger()
    {
        _slots = new OrderedTable.Slot[4];
        _n = 0;
        _tag = 0;
    }

    [Ensures("s.Key == k && s.Next == Pal.Old(s.Next)")]
    private static void SetKey(ref OrderedTable.Slot s, int k)
    {
        s.Key = k;
    }

    // R33.18. An unannotated method with an empty body: its calls are dropped.
    private static void Hook(int k) { }

    // R33.16. An element passed by `ref` is copied in, and the callee's result copied back.
    [Requires("0 <= i && i < @this.SpecSlots.Length")]
    [Ensures("@this.SpecSlots.Length == Pal.Old(@this.SpecSlots).Length && @this.SpecSlots[i].Key == k")]
    public void Rekey(int i, int k)
    {
        ref OrderedTable.Slot s = ref _slots[i];
        SetKey(ref s, k);
        Hook(k);
    }

    [Open]
    [Ensures("Pal.Contents(@this._slots).Length == 4 && @this._n == 0")]
    private void Enlarge()
    {
        _n = 0;
        _slots = new OrderedTable.Slot[4];
    }

    // R33.15, transitively: `Reset` assigns `_tag` neither itself nor through `Enlarge`.
    [Open]
    [Ensures("Pal.Contents(@this._slots).Length == 4 && @this._n == 0")]
    private void Reset()
    {
        Enlarge();
    }

    [Ensures("@this.SpecTag == Pal.Old(@this.SpecTag) && @this.SpecCount == 0")]
    public void Clear()
    {
        Reset();
    }

    // R33.17. The local copy is re-read after the call that may replace the field.
    [Ensures("@this.SpecSlots.Length > 0 && @this.SpecSlots[0].Key == k")]
    public void Grow(int k)
    {
        OrderedTable.Slot[] a = _slots;
        if (_n == a.Length)
        {
            Enlarge();
            a = _slots;
        }
        if (a.Length == 0)
        {
            Enlarge();
            a = _slots;
        }
        a[0].Key = k;
    }

    // R33.20. The loop does not assign `_n` or `_tag`: the invariant need not say so.
    [Open]
    [Requires("0 <= @this._n && @this._n <= Pal.Contents(@this._slots).Length")]
    [Ensures("Pal.Contents(@this._slots).Length == Pal.Old(Pal.Contents(@this._slots)).Length")]
    [Ensures("@this._n == Pal.Old(@this._n) && @this._tag == Pal.Old(@this._tag)")]
    private void ZeroKeys()
    {
        for (int k = 0; k < _n; k++)
        {
            Pal.Invariant(0 <= k && k <= _n);
            Pal.Invariant(Pal.Contents(_slots).Length == Pal.Old(Pal.Contents(this._slots)).Length);
            _slots[k].Key = 0;
        }
    }

    [Ensures("@this.SpecTag == Pal.Old(@this.SpecTag) && @this.SpecCount == Pal.Old(@this.SpecCount)")]
    public void Zero()
    {
        ZeroKeys();
    }

    [Throws(typeof(ArgumentException), "x < 0")]
    [Ensures("Result == x")]
    private static int Checked(int x)
    {
        if (x < 0) throw new ArgumentException();
        return x;
    }

    [Open]
    [Ensures("@this._tag == t && Pal.Contents(@this._slots) == Pal.Old(Pal.Contents(@this._slots))")]
    private void SetTag(int t)
    {
        _tag = t;
    }

    // R33.22. A raising call while `this` is open: `this` is closed around it.
    [Throws(typeof(ArgumentException), "x < 0")]
    [Ensures("@this.SpecTag == x")]
    public void Retag(int x)
    {
        _tag = 0;
        SetTag(Checked(x));
    }

    // R33.21. A `switch` whose arms return or never complete, and an interpolated
    // `Debug.Assert` message.
    [Requires("m == Mode.Keep || m == Mode.Fail || m == Mode.Bump")]
    [Throws(typeof(InvalidOperationException), "!skip && m == Mode.Fail")]
    [Ensures("Result == (skip ? 2 : (m == Mode.Bump ? 1 : 0))")]
    public static int Pick(Mode m, bool skip)
    {
        if (!skip)
        {
            switch (m)
            {
                case Mode.Keep:
                    return 0;
                case Mode.Fail:
                    System.Collections.ThrowHelper.ThrowCycle();
                    break;
                default:
                    Debug.Assert(m == Mode.Bump, $"Unknown mode: {m}");
                    return 1;
            }
        }
        return 2;
    }

    // R33.23. Guards nested in both arms of an `if`/`else`, with a tail after it.
    [Ensures("Result == (b ? (a ? 1 : 2) : 3)")]
    public static int Nested(bool a, bool b)
    {
        int r = 3;
        if (a)
        {
            if (b)
            {
                return 1;
            }
        }
        else
        {
            Debug.Assert(r == 3);
            if (b)
            {
                return 2;
            }
        }
        return r;
    }

    [Ensures("@this.SpecTag == (b ? 1 : 2)")]
    public void NestedVoid(bool a, bool b)
    {
        if (a)
        {
            if (b)
            {
                _tag = 1;
                return;
            }
        }
        else if (b)
        {
            _tag = 1;
            return;
        }
        _tag = 2;
    }
}

// R33.19. `default` of a struct with a field of type-parameter type, as `OrderedDictionary`'s
// `Entry` is.
public class Bag<T>
{
    public struct Cell
    {
        public T Item;
        public int N;

        [Ensures("Result == N")]
        public readonly int Count() => N;
    }

    [Ensures("Result.N == 0")]
    public static Cell Empty()
    {
        Cell c = default;
        return c;
    }
}

// R33.25. A constructor that leaves a nullable comparer field `null` on some path, fills it
// with `c ?? EqualityComparer<T>.Default` or compares it against the default, and builds
// its arrays through an `[Open]` helper.
[Spec]
public struct KeyedModel<T>
{
    public System.Collections.Generic.IEqualityComparer<T>? Comparer;
    public SpecInt Length;
}

[Invariant("_buckets == null || _buckets.Length > 0")]
public class Keyed<T>
{
    private System.Collections.Generic.IEqualityComparer<T>? _comparer;
    private int[]? _buckets;

    [Model]
    private KeyedModel<T> Model => new KeyedModel<T> { Comparer = _comparer, Length = Pal.Contents(_buckets!).Length };

    [Spec] public System.Collections.Generic.IEqualityComparer<T>? SpecComparer => Model.Comparer;
    [Spec] public SpecInt SpecLength => Model.Length;

    [Ensures("Pal.Implies(shared, @this.SpecComparer != null)")]
    [Ensures("Pal.Implies(capacity > 0, @this.SpecLength == capacity)")]
    public Keyed(int capacity, System.Collections.Generic.IEqualityComparer<T>? comparer, bool shared)
    {
        if (capacity > 0)
        {
            Init(capacity);
        }

        if (shared)
        {
            _comparer = comparer ?? System.Collections.Generic.EqualityComparer<T>.Default;
        }
        else if (comparer is not null && comparer != System.Collections.Generic.EqualityComparer<T>.Default)
        {
            _comparer = comparer;
        }
    }

    [Open]
    [Requires("capacity > 0 && @this._buckets == null")]
    [Ensures("@this._buckets != null && Pal.Contents(@this._buckets).Length == capacity")]
    private void Init(int capacity)
    {
        _buckets = new int[capacity];
    }
}

// R33.26. An enumerator in `OrderedDictionary`'s shape: the borrowed object read through a
// local, a `ref` local into its array, and `Current` an auto-property with a private setter.
[Spec]
public struct BookModel<K, V>
{
    public Seq<Book<K, V>.Entry> Entries;
    public SpecInt Count;
    public SpecInt Version;
}

[Invariant("0 <= _count && _count <= _entries.Length")]
public class Book<K, V>
{
    public struct Entry
    {
        public K Key;
        public V Value;
    }

    private Entry[] _entries;
    private int _count;
    [Wrapping] private int _version;

    [Model]
    private BookModel<K, V> Model => new BookModel<K, V> { Entries = Pal.Contents(_entries), Count = _count, Version = _version };

    [Spec] public Seq<Entry> SpecEntries => Model.Entries;
    [Spec] public SpecInt SpecCount => Model.Count;
    [Spec] public SpecInt SpecVersion => Model.Version;

    [Ensures("@this.SpecCount == 0")]
    public Book()
    {
        _entries = new Entry[0];
        _count = 0;
        _version = 0;
    }

    [Ensures("ReferenceEquals(Result._book, @this) && Result._version == @this.SpecVersion && Result._index == 0")]
    public Enumerator GetEnumerator() => new(this);

#pragma warning disable CS8618 // `Current` is `default` until the first `MoveNext`, as in `OrderedDictionary`.
    public struct Enumerator
    {
        private readonly Book<K, V> _book;
        private readonly int _version;
        private int _index;

        [Ensures("ReferenceEquals(@this._book, book) && @this._version == book.SpecVersion && @this._index == 0")]
        internal Enumerator(Book<K, V> book)
        {
            _book = book;
            _version = _book._version;
        }

        public K Current { get; private set; }

        [Requires("0 <= @this._index")]
        [Throws(typeof(InvalidOperationException), "@this._version != @this._book.SpecVersion")]
        [Ensures("@this._version == @this._book.SpecVersion && 0 <= @this._index")]
        [Ensures("Result == (Pal.Old(@this._index) < @this._book.SpecCount)")]
        [Ensures("Pal.Implies(Result, @this._index == Pal.Old(@this._index) + 1 && Pal.Old(@this._index) < @this._book.SpecEntries.Length && Pal.Same(@this.Current, @this._book.SpecEntries[Pal.Old(@this._index)].Key))")]
        [Ensures("Pal.Implies(!Result, @this._index == Pal.Old(@this._index))")]
        public bool MoveNext()
        {
            Book<K, V> book = _book;

            if (_version != book._version)
            {
                throw new InvalidOperationException();
            }

            if (_index < book._count)
            {
                ref Entry entry = ref book._entries[_index];
                Current = entry.Key;
                _index++;
                return true;
            }

            Current = default!;
            return false;
        }
    }
#pragma warning restore CS8618
}
