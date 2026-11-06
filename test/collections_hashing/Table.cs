using System;
using PalLang;

#pragma warning disable CS0649, CS0414

// §24. A hash-table skeleton in the style of dotnet/runtime's `HashSet<T>`: each rule of the
// hashing family that the table's shape needs is exercised by the member that names it.
[assembly: TranslateAnnotatedOnly]

[Spec]
public struct TableModel<T>
{
    public SpecInt Count;
}

// R24.4. Not sealed, but nothing derives from it.
// R24.7. `_buckets` and `_entries` are null until first use; the invariant says so.
[Invariant("0 <= _freeCount && _freeCount <= _count && _count <= _entries.Length")]
[Invariant("(_buckets == null) == (_entries == null)")]
[Invariant("_buckets.Length == _entries.Length")]
[Invariant("_entries != null || _count == 0")]
public class Table<T>
{
    private int[]? _buckets;
    private Entry[]? _entries;
    private int _count;
    private int _freeList;
    private int _freeCount;

    [Model]
    private TableModel<T> Model => new TableModel<T> { Count = _count - _freeCount };

    [Spec] public SpecInt SpecCount => Model.Count;

    [Ensures("@this.SpecCount == 0")]
    public Table()
    {
        _buckets = null;
        _entries = null;
        _count = 0;
        _freeList = 0;
        _freeCount = 0;
    }

    [Ensures("Result == @this.SpecCount")]
    public int Count => _count - _freeCount;

    // R24.7: a code-level null test of a nullable array field.
    [Ensures("Result == (@this.SpecCount > 0)")]
    public bool Any() => _buckets != null && _count - _freeCount > 0;

    // R24.10: one-argument `Array.Clear`; R24.11: clearing needs a default for `Entry`.
    [Ensures("@this.SpecCount == 0")]
    public void Clear()
    {
        int count = _count;
        if (count > 0)
        {
            Array.Clear(_buckets!);
            _count = 0;
            _freeList = -1;
            _freeCount = 0;
            Array.Clear(_entries!, 0, count);
        }
    }

    // R24.7: replacing a nullable array field.
    [Ensures("@this.SpecCount == 0")]
    public void Reset(int size)
    {
        if (size < 1) size = 1;
        _buckets = new int[size];
        _entries = new Entry[size];
        _count = 0;
        _freeList = -1;
        _freeCount = 0;
    }

    // R24.6: a struct nested in a generic class.
    private struct Entry
    {
        public int HashCode;
        public int Next;
        public T Value;
    }
}
