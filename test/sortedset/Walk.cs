// R27.35. A stack of pointers into a region: an in-order walk of the tree, as
// dotnet/runtime's `SortedSet<T>.InOrderTreeWalk` and its enumerator walk it. The stack is
// an ordinary object holding pointers; what it owes is a pure function of the owner's heap
// (`SpecWalk`).
using System.Collections.Generic;
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

    // R27.40. A class indexer, read in code, is a call of its getter.
    public T this[int index]
    {
        [Requires("0 <= index && index < @this.SpecCount")]
        [Ensures("Pal.Same(Result, @this.Items[index])")]
        get => _array[index];
    }

    [Ensures("Result == (0 < Pal.Old(@this.SpecCount))")]
    [Ensures("Pal.Implies(Result, Pal.Same(result, Pal.Old(@this.Items)[Pal.Old(@this.SpecCount) - 1]))")]
    [Ensures("@this.Items == Pal.Slice(Pal.Old(@this.Items), 0, Result ? Pal.Old(@this.SpecCount) - 1 : Pal.Old(@this.SpecCount))")]
    [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
    public bool TryPop(out T result)
    {
        int size = _size - 1;
        if (size < 0)
        {
            result = default!;
            return false;
        }
        _size = size;
        result = _array[size];
        return true;
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

internal delegate bool WalkPredicate<T>(WalkSet<T>.WNode node);

[Spec]
public struct CounterModel
{
    public SpecInt Value;
}

[Invariant("0 <= _n")]
public sealed class Counter
{
    private int _n;

    [Model] private CounterModel Model => new CounterModel { Value = _n };
    [Spec] public SpecInt SpecValue => Model.Value;

    [Ensures("@this.SpecValue == 0")]
    public Counter() { _n = 0; }

    [Ensures("Result == @this.SpecValue && 0 <= Result")]
    public int Value => _n;

    [Requires("@this.SpecValue < int.MaxValue")]
    [Ensures("@this.SpecValue == Pal.Old(@this.SpecValue) + 1")]
    public void Increment() { _n++; }
}

public static class Filters
{
    // R27.40. A `void` `[SpecOp]` is a lemma, called as a ghost statement.
    [Requires("Pal.StrictlySorted(c, Pal.Contents(a))")]
    [Ensures("SpecSetFilter.Removing(c, Pal.Contents(a), Pal.Contents(a), Pal.Slice(Pal.Contents(a), 0, 0), -1)")]
    public static void NothingRemoved(System.Collections.Generic.IComparer<int> c, int[] a)
    {
        SpecSetFilter.RemovingStart(c, Pal.Contents(a), Pal.Slice(Pal.Contents(a), 0, 0));
    }

    // R27.40. A loop that may return, with an `if` whose arms call a method on a local
    // object: what follows is checked in each arm, so what the call ensured is kept.
    [Requires("0 <= n")]
    [Ensures("0 <= Result && Result <= n")]
    public static int FillUntil(int n, int stop)
    {
        var bag = new PtrStack<int>(n);
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(Pal.Returned()
                              ? 0 <= Pal.ReturnValue<int>() && Pal.ReturnValue<int>() <= n
                              : 0 <= i && i <= n && bag.SpecCount == i && bag.SpecCapacity == n);
            Pal.Decreases(n - i);
            if (i == stop)
            {
                return i;
            }
            if (i % 2 == 0)
            {
                bag.Push(i);
            }
            else
            {
                bag.Push(-i);
            }
            int x = bag[i];
            Pal.Assert(x == i || x == -i);
            i++;
        }
        return n;
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

    [Refine("Result.Count == Result.Tree.Size && Result.Count <= int.MaxValue")]
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
    [Rlimit(4)]
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


    // R27.39. A walk that calls back: what the callback was called on, and what it returned,
    // is the trace the caller's protocol is kept over.
    [Ensures("SpecWalk.Walked(@this.SpecItems, Pal.Trace<(T, bool), bool>(action), Result)")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Rlimit(4)]
    internal bool InOrderTreeWalk([Callback] WalkPredicate<T> action)
    {
        if (root == null)
        {
            return true;
        }
        var stack = new PtrStack<WNode>(count);
        WNode? current = root;
        SpecWalk.Empty<WNode, T>(false, Pal.Heap<WNode>(), stack.Items);
        while (current != null)
        {
            Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
            Pal.Invariant(Pal.WellFormed(current) && SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), stack.Items) &&
                          stack.SpecCapacity == count && SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                          Pal.Trace<(T, bool), bool>(action).Length == 0 &&
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
                          0 <= n && n <= count &&
                          SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                          (Pal.Returned()
                              ? !Pal.ReturnValue<bool>() &&
                                SpecWalk.Walked(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action), false)
                              : Pal.Trace<(T, bool), bool>(action).Length == n &&
                                SpecWalk.Visited(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action)) &&
                                SpecWalk.Pending<WNode, T>(false, Pal.Heap<WNode>(), stack.Items) ==
                                Pal.Slice(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), n, count)));
            SpecWalk.PopAt<WNode, T>(false, Pal.Heap<WNode>(), stack.Items, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), n);
            current = stack.Pop();
            if (!action(current))
            {
                return false;
            }
            n++;
            WNode? node = current.Right;
            while (node != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                Pal.Invariant(Pal.WellFormed(node) && SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), stack.Items) &&
                              stack.SpecCapacity == count && 0 < n && n <= count &&
                              SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                              Pal.Trace<(T, bool), bool>(action).Length == n &&
                              SpecWalk.Visited(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action)) &&
                              Pal.Concat(SpecWalk.Keys(false, Pal.Tree<(T, bool)>(node)),
                                         SpecWalk.Pending<WNode, T>(false, Pal.Heap<WNode>(), stack.Items)) ==
                              Pal.Slice(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), n, count));
                SpecWalk.Descend<WNode, T>(false, Pal.Heap<WNode>(), stack.Items, node);
                Pal.Assert(stack.Items.Length < count - n);
                stack.Push(node);
                node = node.Left;
            }
        }
        return true;
    }

    // R27.39. `SortedSet<T>.CopyTo(T[], int, int)`: a lambda that writes a captured index.
    [Requires("0 <= index && 0 <= count && index <= array.Length - count")]
    [Ensures("SpecWalk.CopyResult(@this.SpecItems, Pal.Old(Pal.Contents(array)), Pal.Contents(array), index, index + count)")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    internal void CopyTo(T[] array, int index, int count)
    {
        if (index > array.Length - count)
        {
            throw new System.ArgumentException();
        }
        count += index;
        Ghost<SpecInt> i0 = (SpecInt)index;
        Ghost<Seq<T>> a0 = Pal.Contents(array);
        InOrderTreeWalk(node =>
        {
            Pal.Protocol<(T, bool), bool>(tr => SpecWalk.Copied(tr, a0.Value, Pal.Contents(array), i0.Value, count, index));
            if (index >= count)
            {
                return false;
            }
            array[index++] = node.Item;
            return true;
        });
    }

    [Ensures("ReferenceEquals(Result._tree, @this) && Result._version == @this.SpecVersion && !Result._reverse")]
    [Ensures("SpecWalk.Walkable<WalkSet<T>.WNode, T>(Pal.Heap<WalkSet<T>.WNode>(), Result._stack.Items)")]
    [Ensures("SpecWalk.Pending<WalkSet<T>.WNode, T>(false, Pal.Heap<WalkSet<T>.WNode>(), Result._stack.Items) == @this.SpecItems")]
    [Ensures("Result._stack.SpecCapacity == @this.SpecCount")]
    public Enumerator GetEnumerator() => new Enumerator(this, false);

    // R27.41. A method that holds an enumerator of its own set and calls its members.
    [Ensures("Result == @this.SpecItems.Length")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Rlimit(4)]
    internal int CountByEnumerator()
    {
        Enumerator e = new Enumerator(this, false);
        int n = 0;
        while (e.MoveNext())
        {
            Pal.Invariant(e.SpecReady && n + e.SpecPending.Length == this.SpecItems.Length);
            Pal.Decreases(this.SpecItems.Length - n);
            n++;
        }
        return n;
    }

    // R27.49. A method that holds an enumerator of its own set and one of another set.
    [Ensures("Result <= @this.SpecItems.Length && Result <= other.SpecItems.Length")]
    [Ensures("Result == @this.SpecItems.Length || Result == other.SpecItems.Length")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Rlimit(8)]
    internal int CountPairs(WalkSet<T> other)
    {
        Enumerator mine = GetEnumerator();
        Enumerator theirs = other.GetEnumerator();
        int n = 0;
        bool mineEnded = !mine.MoveNext();
        bool theirsEnded = !theirs.MoveNext();
        while (!mineEnded && !theirsEnded)
        {
            Pal.Invariant(mine.SpecReady && theirs.SpecReady &&
                          n + (mineEnded ? 0 : 1) + mine.SpecPending.Length == this.SpecItems.Length &&
                          n + (theirsEnded ? 0 : 1) + theirs.SpecPending.Length == other.SpecItems.Length &&
                          (!mineEnded || mine.SpecPending.Length == 0) && (!theirsEnded || theirs.SpecPending.Length == 0));
            Pal.Decreases(this.SpecItems.Length - n);
            n++;
            mineEnded = !mine.MoveNext();
            theirsEnded = !theirs.MoveNext();
        }
        return n;
    }

    [Ensures("Result == @this.SpecItems.Length")]
    public int Count => count;

    // R27.51. `foreach` over another set: its enumerator, held, named `Pal.Enumerator<E>(x)`.
    [Ensures("Result == other.SpecItems.Length")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Rlimit(4)]
    internal int CountOther(WalkSet<T> other)
    {
        int n = 0;
        foreach (T item in other)
        {
            Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecReady &&
                          n + Pal.Enumerator<Enumerator>(item).SpecPending.Length == other.SpecItems.Length);
            Pal.Decreases(other.SpecItems.Length - n);
            n++;
        }
        return n;
    }

    // R27.50. Two owners held whole are distinct objects, so `other == this` is false;
    // the loop calls a method on the receiver, whose model the loop keeps because the
    // method has not written it yet; the write comes after.
    [Ensures("Result == -1 || Result == Pal.Old(@this.SpecItems).Length || Result == other.SpecItems.Length")]
    [Ensures("Result != -1")]
    [Ensures("@this.SpecItems == Pal.Old(@this.SpecItems)")]
    [Rlimit(8)]
    internal int CountPairsThenTouch(WalkSet<T> other)
    {
        if (other == this)
        {
            return -1;
        }
        Enumerator mine = GetEnumerator();
        Enumerator theirs = other.GetEnumerator();
        int n = 0;
        bool mineEnded = !mine.MoveNext();
        bool theirsEnded = !theirs.MoveNext();
        while (!mineEnded && !theirsEnded && n < Count)
        {
            Pal.Invariant(mine.SpecReady && theirs.SpecReady &&
                          n + (mineEnded ? 0 : 1) + mine.SpecPending.Length == this.SpecItems.Length &&
                          n + (theirsEnded ? 0 : 1) + theirs.SpecPending.Length == other.SpecItems.Length &&
                          (!mineEnded || mine.SpecPending.Length == 0) && (!theirsEnded || theirs.SpecPending.Length == 0));
            Pal.Decreases(this.SpecItems.Length - n);
            n++;
            mineEnded = !mine.MoveNext();
            theirsEnded = !theirs.MoveNext();
        }
        version++;
        return n;
    }

    // R27.49. Two enumerators walked in step, declared in a nested block: the sets'
    // in-order sequences compare equal position by position.
    [Ensures("Pal.Implies(walk, Result == SpecSetCompare.SameKeys(c, @this.SpecItems, other.SpecItems))")]
    [Rlimit(8)]
    internal bool SameKeysAs(WalkSet<T> other, IComparer<T> c, bool walk)
    {
        if (walk)
        {
            Enumerator mine = GetEnumerator();
            Enumerator theirs = other.GetEnumerator();
            bool mineEnded = !mine.MoveNext();
            bool theirsEnded = !theirs.MoveNext();
            SpecSetCompare.SameKeysWhole(c, this.SpecItems, other.SpecItems);
            while (!mineEnded && !theirsEnded)
            {
                Pal.Invariant(mine.SpecReady && theirs.SpecReady &&
                              (Pal.Returned()
                                  ? !Pal.ReturnValue<bool>() && !SpecSetCompare.SameKeys(c, this.SpecItems, other.SpecItems)
                                  : Pal.Implies(mineEnded, mine.SpecPending.Length == 0) &&
                                    Pal.Implies(theirsEnded, theirs.SpecPending.Length == 0) &&
                                    mine.SpecPending == Pal.Slice(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length, this.SpecItems.Length) &&
                                    theirs.SpecPending == Pal.Slice(other.SpecItems, other.SpecItems.Length - theirs.SpecPending.Length, other.SpecItems.Length) &&
                                    Pal.Implies(!mineEnded, mine.SpecCurrentIn && mine.SpecPending.Length < this.SpecItems.Length &&
                                        Pal.Same(SpecSearchTree.RootKey(mine.SpecCurrentTree, this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1]),
                                                 this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1])) &&
                                    Pal.Implies(!theirsEnded, theirs.SpecCurrentIn && theirs.SpecPending.Length < other.SpecItems.Length &&
                                        Pal.Same(SpecSearchTree.RootKey(theirs.SpecCurrentTree, other.SpecItems[other.SpecItems.Length - theirs.SpecPending.Length - 1]),
                                                 other.SpecItems[other.SpecItems.Length - theirs.SpecPending.Length - 1])) &&
                                    SpecSetCompare.SameKeys(c, this.SpecItems, other.SpecItems) ==
                                    SpecSetCompare.SameKeys(c,
                                        Pal.Slice(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1), this.SpecItems.Length),
                                        Pal.Slice(other.SpecItems, other.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1), other.SpecItems.Length))));
                Pal.Decreases(mine.SpecPending.Length + (mineEnded ? 0 : 1));
                SpecSetCompare.SameKeysStep(c, this.SpecItems, other.SpecItems,
                    this.SpecItems.Length - mine.SpecPending.Length - 1, other.SpecItems.Length - theirs.SpecPending.Length - 1);
                if (c.Compare(mine.Current, theirs.Current) != 0)
                {
                    return false;
                }
                mineEnded = !mine.MoveNext();
                theirsEnded = !theirs.MoveNext();
            }
            SpecSetCompare.SameKeysStep(c, this.SpecItems, other.SpecItems,
                this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1),
                other.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1));
            return mineEnded && theirsEnded;
        }
        return false;
    }

    // R27.42. An iterator method: verified as one whole enumeration of what it yields.
    [Ensures("Pal.Yielded<T>() == Pal.Reverse(@this.SpecItems)")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Rlimit(4)]
    public IEnumerable<T> Reverse()
    {
        Enumerator e = new Enumerator(this, true);
        while (e.MoveNext())
        {
            Pal.Invariant(e.SpecReady && Pal.Concat(Pal.Yielded<T>(), e.SpecPending) == Pal.Reverse(this.SpecItems));
            Pal.Decreases(this.SpecItems.Length - Pal.Yielded<T>().Length);
            yield return e.Current;
        }
    }

    // R27.37. An enumerator that owns a stack of pointers into the set's region.
    public struct Enumerator
    {
        private readonly WalkSet<T> _tree;
        private readonly int _version;
        private readonly PtrStack<WNode> _stack;
        private WNode? _current;
        private readonly bool _reverse;

        // R27.41. What a holder of the enumerator states of it.
        [Spec] internal Seq<T> SpecPending => SpecWalk.Pending<WNode, T>(_reverse, Pal.Heap<WNode>(), _stack.Items);
        [Spec] internal SpecTree<(T, bool)> SpecCurrentTree => Pal.Tree<(T, bool)>(_current);
        [Spec] internal bool SpecCurrentIn => _current != null && Pal.InRegion(_current);
        [Spec] internal bool SpecReady =>
            SpecWalk.Walkable<WNode, T>(Pal.Heap<WNode>(), _stack.Items) && _stack.SpecCapacity == _tree.SpecCount &&
            SpecPending.Length <= _tree.SpecCount && _version == _tree.SpecVersion;

        [Ensures("ReferenceEquals(@this._tree, set) && @this._version == set.SpecVersion && @this._reverse == reverse")]
        [Ensures("SpecWalk.Walkable<WalkSet<T>.WNode, T>(Pal.Heap<WalkSet<T>.WNode>(), @this._stack.Items)")]
        [Ensures("@this._stack.SpecCapacity == set.SpecCount")]
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

    // R27.40. A lambda that captures an object (and a delegate, whose null guard is nothing).
    [Ensures("0 <= Result")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    internal int CountWhere(System.Predicate<T> match)
    {
        System.ArgumentNullException.ThrowIfNull(match);
        Counter counter = new Counter();
        InOrderTreeWalk(node =>
        {
            Pal.Protocol<(T, bool), bool>(tr => counter.SpecValue <= tr.Length);
            if (match(node.Item))
            {
                counter.Increment();
            }
            return true;
        });
        return counter.Value;
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
