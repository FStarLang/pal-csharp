// R27.35. A stack of pointers into a region: an in-order walk of the tree, as
// dotnet/runtime's `SortedSet<T>.InOrderTreeWalk` and its enumerator walk it. The stack is
// an ordinary object holding pointers; what it owes is a pure function of the owner's heap
// (`SpecWalk`).
using PalLang;
#pragma warning disable CS0649

[Spec]
public struct PtrStackModel<T>
{
    public Seq<T> Items;
    public SpecInt Capacity;
}

[Invariant("0 <= _size")]
[Invariant("_size <= _array.Length")]
public sealed class PtrStack<T>
{
    private T[] _array;
    private int _size;

    [Refine("Result.Items.Length <= Result.Capacity")]
    [Model]
    private PtrStackModel<T> Model => new PtrStackModel<T>
    {
        Items = Pal.Slice(Pal.Contents(_array), 0, _size),
        Capacity = _array.Length,
    };

    [Spec] public Seq<T> Items => Model.Items;
    [Spec] public SpecInt SpecCount => Model.Items.Length;
    [Spec] public SpecInt SpecCapacity => Model.Capacity;

    [Requires("0 <= capacity")]
    [Ensures("@this.SpecCount == 0 && @this.SpecCapacity == capacity")]
    public PtrStack(int capacity)
    {
        _array = new T[capacity];
        _size = 0;
    }

    [Ensures("Result == @this.SpecCount")]
    public int Count => _size;

    [Requires("@this.SpecCount < @this.SpecCapacity")]
    [Ensures("@this.Items == Pal.Snoc(Pal.Old(@this.Items), item)")]
    [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
    public void Push(T item)
    {
        _array[_size] = item;
        _size++;
    }

    [Ensures("@this.SpecCount == 0")]
    [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
    public void Clear()
    {
        _size = 0;
    }

    [Requires("0 < @this.SpecCount")]
    [Ensures("Pal.Same(Result, Pal.Old(@this.Items)[Pal.Old(@this.SpecCount) - 1])")]
    [Ensures("@this.Items == Pal.Slice(Pal.Old(@this.Items), 0, Pal.Old(@this.SpecCount) - 1)")]
    [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
    public T Pop()
    {
        _size--;
        return _array[_size];
    }
}

[Spec]
public struct WalkModel<T>
{
    public SpecTree<(T, bool)> Tree;
    public SpecInt Count;
    public SpecInt Version;
}

public sealed class WalkSet<T>
{
    private WNode? root;
    private int count;
    [Wrapping] private int version;

    [Refine("Result.Count == Result.Tree.Size")]
    [Model]
    private WalkModel<T> Model => new WalkModel<T> { Tree = Pal.Tree<(T, bool)>(root), Count = count, Version = version };

    [Spec] public SpecTree<(T, bool)> SpecNodes => Model.Tree;
    [Spec] public Seq<T> SpecItems => SpecSearchTree.Keys(Model.Tree);
    [Spec] public SpecInt SpecVersion => Model.Version;
    [Spec] public SpecInt SpecCount => Model.Count;

    [Ensures("@this.SpecItems.Length == 0")]
    public WalkSet()
    {
        root = null;
        count = 0;
    }

    // R27.35. A local stack of region pointers: the walk visits every node once.
    [Ensures("Result == @this.SpecItems.Length")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    internal int CountInOrder()
    {
        var stack = new PtrStack<WNode>(count);
        WNode? current = root;
        SpecWalk.Empty<WNode, T>(false, Pal.Heap<WNode>(), stack.Items);
        while (current != null)
        {
            Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
            Pal.Invariant(Pal.WellFormed(current) && SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), stack.Items) &&
                          stack.SpecCapacity == count && SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                          Pal.Concat(SpecWalk.Keys(false, Pal.Tree<(T, bool)>(current)),
                                     SpecWalk.Pending<WNode, T>(false, Pal.Heap<WNode>(), stack.Items)) ==
                          SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)));
            SpecWalk.Descend<WNode, T>(false, Pal.Heap<WNode>(), stack.Items, current);
            stack.Push(current);
            current = current.Left;
        }

        int n = 0;
        while (stack.Count != 0)
        {
            Pal.Decreases(count - n);
            Pal.Invariant(SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), stack.Items) && stack.SpecCapacity == count &&
                          SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                          0 <= n && n + SpecWalk.Pending<WNode, T>(false, Pal.Heap<WNode>(), stack.Items).Length == count);
            SpecWalk.Pop<WNode, T>(false, Pal.Heap<WNode>(), stack.Items);
            WNode next = stack.Pop();
            n++;
            WNode? node = next.Right;
            while (node != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                Pal.Invariant(Pal.WellFormed(node) && SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), stack.Items) &&
                              stack.SpecCapacity == count && 0 < n && SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                              n + SpecWalk.Keys(false, Pal.Tree<(T, bool)>(node)).Length +
                              SpecWalk.Pending<WNode, T>(false, Pal.Heap<WNode>(), stack.Items).Length == count);
                    SpecWalk.Descend<WNode, T>(false, Pal.Heap<WNode>(), stack.Items, node);
                stack.Push(node);
                node = node.Left;
            }
        }
        return n;
    }

    // R27.35. The walk yields the keys in order.
    [Requires("array.Length == @this.SpecItems.Length")]
    [Ensures("Pal.Contents(array) == @this.SpecItems")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    internal void CopyInOrder(T[] array)
    {
        var stack = new PtrStack<WNode>(count);
        WNode? current = root;
        SpecWalk.Empty<WNode, T>(false, Pal.Heap<WNode>(), stack.Items);
        while (current != null)
        {
            Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
            Pal.Invariant(Pal.WellFormed(current) && SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), stack.Items) &&
                          stack.SpecCapacity == count && SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                          Pal.Concat(SpecWalk.Keys(false, Pal.Tree<(T, bool)>(current)),
                                     SpecWalk.Pending<WNode, T>(false, Pal.Heap<WNode>(), stack.Items)) ==
                          SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)));
            SpecWalk.Descend<WNode, T>(false, Pal.Heap<WNode>(), stack.Items, current);
            stack.Push(current);
            current = current.Left;
        }

        int n = 0;
        while (stack.Count != 0)
        {
            Pal.Decreases(count - n);
            Pal.Invariant(SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), stack.Items) && stack.SpecCapacity == count &&
                          array.Length == count && 0 <= n && n <= count &&
                          SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                          Pal.Forall((int i) => Pal.Implies(0 <= i && i < n, Pal.Same(Pal.Contents(array)[i], SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root))[i]))) &&
                          SpecWalk.Pending<WNode, T>(false, Pal.Heap<WNode>(), stack.Items) ==
                          Pal.Slice(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), n, count));
            SpecWalk.PopAt<WNode, T>(false, Pal.Heap<WNode>(), stack.Items, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), n);
            WNode next = stack.Pop();
            array[n] = next.Item;
            n++;
            WNode? node = next.Right;
            while (node != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                Pal.Invariant(Pal.WellFormed(node) && SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), stack.Items) &&
                              stack.SpecCapacity == count && array.Length == count && 0 < n && n <= count &&
                              SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                              Pal.Forall((int i) => Pal.Implies(0 <= i && i < n, Pal.Same(Pal.Contents(array)[i], SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root))[i]))) &&
                              Pal.Concat(SpecWalk.Keys(false, Pal.Tree<(T, bool)>(node)),
                                         SpecWalk.Pending<WNode, T>(false, Pal.Heap<WNode>(), stack.Items)) ==
                              Pal.Slice(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), n, count));
                SpecWalk.Descend<WNode, T>(false, Pal.Heap<WNode>(), stack.Items, node);
                stack.Push(node);
                node = node.Left;
            }
        }
        Pal.Assert(Pal.Slice(Pal.Contents(array), 0, n) == SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)));
    }


    [Ensures("ReferenceEquals(Result._tree, @this) && Result._version == @this.SpecVersion && !Result._reverse")]
    [Ensures("SpecWalk.Walkable<WalkSet<T>.WNode, T>(Pal.Heap<WalkSet<T>.WNode>(), Result._stack.Items)")]
    [Ensures("SpecWalk.Pending<WalkSet<T>.WNode, T>(false, Pal.Heap<WalkSet<T>.WNode>(), Result._stack.Items) == @this.SpecItems")]
    public Enumerator GetEnumerator() => new Enumerator(this, false);

    // R27.37. An enumerator that owns a stack of pointers into the set's region.
    public struct Enumerator
    {
        private readonly WalkSet<T> _tree;
        private readonly int _version;
        private readonly PtrStack<WNode> _stack;
        private WNode? _current;
        private readonly bool _reverse;

        [Ensures("ReferenceEquals(@this._tree, set) && @this._version == set.SpecVersion && @this._reverse == reverse")]
        [Ensures("SpecWalk.Walkable<WalkSet<T>.WNode, T>(Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)")]
        [Ensures("SpecWalk.Pending<WalkSet<T>.WNode, T>(reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items) == (reverse ? Pal.Reverse(set.SpecItems) : set.SpecItems)")]
        internal Enumerator(WalkSet<T> set, bool reverse)
        {
            _tree = set;
            _version = set.version;
            _stack = new PtrStack<WNode>(set.count);
            _current = null;
            _reverse = reverse;
            Initialize();
        }

        [Requires("@this._stack.SpecCount == 0 && @this._stack.SpecCapacity == @this._tree.SpecCount")]
        [Ensures("SpecWalk.Walkable<WalkSet<T>.WNode, T>(Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)")]
        [Ensures("@this._stack.SpecCapacity == @this._tree.SpecCount")]
        [Ensures("SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items) == SpecWalk.Keys(@this._reverse, @this._tree.SpecNodes)")]
        private void Initialize()
        {
            _current = null;
            WNode? node = _tree.root;
            SpecWalk.Empty<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items);
            while (node != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                Pal.Invariant(Pal.WellFormed(node) && SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), _stack.Items) &&
                              _stack.SpecCapacity == _tree.count &&
                              Pal.Concat(SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(node)),
                                         SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items)) ==
                              SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(_tree.root)));
                SpecWalk.Descend<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items, node);
                _stack.Push(node);
                node = _reverse ? node.Right : node.Left;
            }
            Pal.Assert(Pal.Concat(SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(node)),
                                  SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items)) ==
                       SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items));
            Pal.Assert(SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items) == SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(_tree.root)));
        }

        [Requires("SpecWalk.Walkable<WalkSet<T>.WNode, T>(Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)")]
        [Requires("@this._stack.SpecCapacity == @this._tree.SpecCount")]
        [Requires("SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items).Length <= @this._tree.SpecCount")]
        [Throws(typeof(System.InvalidOperationException), "@this._version != @this._tree.SpecVersion")]
        [Ensures("SpecWalk.Walkable<WalkSet<T>.WNode, T>(Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)")]
        [Ensures("@this._stack.SpecCapacity == @this._tree.SpecCount")]
        [Ensures("Result == (Pal.Old(SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)).Length > 0)")]
        [Ensures("Pal.Implies(!Result, @this._current == null)")]
        [Ensures("Pal.Implies(Result, @this._current != null && Pal.WellFormed(@this._current) && " +
                 "Pal.Same(SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(@this._current), Pal.Old(SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items))[0]), " +
                 "Pal.Old(SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items))[0]))")]
        [Ensures("SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items) == " +
                 "Pal.Slice(Pal.Old(SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)), Result ? 1 : 0, " +
                 "Pal.Old(SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)).Length)")]
        public bool MoveNext()
        {
            if (_version != _tree.version)
            {
                throw new System.InvalidOperationException();
            }

            if (_stack.Count == 0)
            {
                _current = null;
                return false;
            }

            Ghost<Seq<T>> p0 = SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items);
            Pal.Assert(SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items) == Pal.Slice(p0.Value, 0, p0.Value.Length));
            SpecWalk.PopAt<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items, p0.Value, 0);
            _current = _stack.Pop();
            WNode? node = _reverse ? _current.Left : _current.Right;
            while (node != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                Pal.Invariant(Pal.WellFormed(node) && SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), _stack.Items) &&
                              _stack.SpecCapacity == _tree.count && p0.Value.Length <= _tree.count &&
                              Pal.Concat(SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(node)),
                                         SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items)) ==
                              Pal.Slice(p0.Value, 1, p0.Value.Length));
                SpecWalk.Length<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items);
                SpecWalk.Descend<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items, node);
                _stack.Push(node);
                node = _reverse ? node.Right : node.Left;
            }
            Pal.Assert(Pal.Concat(SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(node)),
                                  SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items)) ==
                       SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items));
            return true;
        }

        [Requires("@this._current == null || Pal.InRegion(@this._current)")]
        [Ensures("Pal.Implies(@this._current != null, Pal.Same(Result, SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(@this._current), Result)))")]
        public T Current
        {
            get
            {
                if (_current != null)
                {
                    return _current.Item;
                }
                return default(T)!;
            }
        }

        [Requires("@this._stack.SpecCapacity == @this._tree.SpecCount")]
        [Throws(typeof(System.InvalidOperationException), "@this._version != @this._tree.SpecVersion")]
        [Ensures("SpecWalk.Walkable<WalkSet<T>.WNode, T>(Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)")]
        [Ensures("@this._stack.SpecCapacity == @this._tree.SpecCount")]
        [Ensures("SpecWalk.Pending<WalkSet<T>.WNode, T>(@this._reverse, Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items) == SpecWalk.Keys(@this._reverse, @this._tree.SpecNodes)")]
        internal void Reset()
        {
            if (_version != _tree.version)
            {
                throw new System.InvalidOperationException();
            }
            _stack.Clear();
            Initialize();
        }
    }

    [Region]
    internal sealed class WNode
    {
        public T Item;
        public WNode? Left;
        public WNode? Right;
        public bool IsRed;

        public WNode(T item, bool isRed)
        {
            Item = item;
            IsRed = isRed;
        }

        [Model]
        private (T, bool) View => (Item, IsRed);
    }
}
