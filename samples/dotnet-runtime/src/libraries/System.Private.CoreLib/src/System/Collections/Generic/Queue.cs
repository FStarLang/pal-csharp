// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using PalLang;

namespace System.Collections.Generic
{
    /// <summary>
    /// The abstract state of a <see cref="Queue{T}"/>: its elements, oldest first, and its
    /// capacity; and, so that the representation is determined by it, the backing store
    /// and the head's position in it.
    /// </summary>
    [Spec]
    public struct QueueModel<T>
    {
        public Seq<T> Items;
        public SpecInt Capacity;
        public Seq<T> Store;
        public SpecInt Head;
        /// <summary>The modification counter an enumerator checks.</summary>
        public SpecInt Version;
    }

    /// <summary>
    /// Represents a first-in, first-out collection of objects.
    /// </summary>
    /// <remarks>
    /// Implemented as a circular buffer, so <see cref="Enqueue(T)"/> and <see cref="Dequeue"/> are typically <c>O(1)</c>.
    /// </remarks>
    [DebuggerTypeProxy(typeof(QueueDebugView<>))]
    [DebuggerDisplay("Count = {Count}")]
    [Serializable]
    [TypeForwardedFrom("System, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    [Invariant("0 <= _size")]
    [Invariant("_size <= _array.Length")]
    [Invariant("0 <= _head")]
    [Invariant("_head < _array.Length || _head == 0")]
    [Invariant("_tail == (_head + _size < _array.Length ? _head + _size : _head + _size - _array.Length)")]
    public class Queue<T> : IEnumerable<T>,
        ICollection,
        IReadOnlyCollection<T>
    {
        private T[] _array;
        private int _head;       // The index from which to dequeue if the queue isn't empty.
        private int _tail;       // The index at which to enqueue if the queue isn't full.
        private int _size;       // Number of elements.
        [Wrapping] private int _version;

        [Refine("Result.Items.Length <= Result.Capacity")]
        [Refine("Result.Store.Length == Result.Capacity")]
        [Model]
        private QueueModel<T> Model => new QueueModel<T>
        {
            Items = Pal.Ring(Pal.Contents(_array), _head, _size),
            Capacity = _array.Length,
            Store = Pal.Contents(_array),
            Head = _head,
            Version = _version,
        };

        /// <summary>The elements, oldest first: the next to be dequeued is the first.</summary>
        [Spec]
        public Seq<T> Items => Model.Items;

        [Spec]
        public SpecInt SpecCount => Model.Items.Length;

        [Spec]
        public SpecInt SpecCapacity => Model.Capacity;

        [Spec]
        public SpecInt SpecVersion => Model.Version;

        [Spec]
        public SpecInt SpecHead => Model.Head;

        // Creates a queue with room for capacity objects. The default initial
        // capacity and grow factor are used.
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == 0")]
        public Queue()
        {
            _array = [];
        }

        // Creates a queue with room for capacity objects. The default grow factor
        // is used.
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == capacity")]
        public Queue(int capacity)
        {
            ArgumentOutOfRangeException.ThrowIfNegative(capacity);
            _array = new T[capacity];
        }

        // Fills a Queue with the elements of an ICollection.  Uses the enumerator
        // to get each of the elements.
        [Ensures("@this.Items == Pal.Contents(collection)")]
        public Queue(IEnumerable<T> collection)
        {
            ArgumentNullException.ThrowIfNull(collection);

            _array = EnumerableHelpers.ToArray(collection, out _size);
            if (_size != _array.Length) _tail = _size;
        }

        [Ensures("Result == @this.SpecCount")]
        public int Count => _size;

        /// <summary>
        /// Gets the total numbers of elements the internal data structure can hold without resizing.
        /// </summary>
        [Ensures("Result == @this.SpecCapacity")]
        public int Capacity => _array.Length;

        /// <inheritdoc cref="ICollection.IsSynchronized" />
        bool ICollection.IsSynchronized => false;

        object ICollection.SyncRoot => this;

        // Removes all Objects from the queue.
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        public void Clear()
        {
            if (_size != 0)
            {
                if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
                {
                    if (_head < _tail)
                    {
                        Array.Clear(_array, _head, _size);
                    }
                    else
                    {
                        Array.Clear(_array, _head, _array.Length - _head);
                        Array.Clear(_array, 0, _tail);
                    }
                }

                _size = 0;
            }

            _head = 0;
            _tail = 0;
            _version++;
        }

        // CopyTo copies a collection into an Array, starting at a particular
        // index into the array.
        [Throws(typeof(ArgumentOutOfRangeException), "arrayIndex < 0 || arrayIndex > Pal.Contents(array).Length")]
        [Throws(typeof(ArgumentException), "Pal.Contents(array).Length - arrayIndex < @this.SpecCount")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("0 <= arrayIndex && Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), arrayIndex, arrayIndex + @this.SpecCount, @this.Items)")]
        // pal: `arrayIndex + _array.Length - _head` below can overflow in its first addition
        // (a large queue copied near the end of a large array); unchecked, it wraps back to
        // the in-range destination, so the method is verified as `[Wrapping]`.
        [Wrapping]
        public void CopyTo(T[] array, int arrayIndex)
        {
            ArgumentNullException.ThrowIfNull(array);

            if (arrayIndex < 0 || arrayIndex > array.Length)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.arrayIndex, ExceptionResource.ArgumentOutOfRange_IndexMustBeLessOrEqual);
            }

            if (array.Length - arrayIndex < _size)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Argument_InvalidOffLen);
            }

            int numToCopy = _size;
            if (numToCopy == 0) return;

            int firstPart = Math.Min(_array.Length - _head, numToCopy);
            Array.Copy(_array, _head, array, arrayIndex, firstPart);
            numToCopy -= firstPart;
            if (numToCopy > 0)
            {
                Array.Copy(_array, 0, array, arrayIndex + _array.Length - _head, numToCopy);
            }
        }

        void ICollection.CopyTo(Array array, int index)
        {
            ArgumentNullException.ThrowIfNull(array);

            if (array.Rank != 1)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_RankMultiDimNotSupported, ExceptionArgument.array);
            }

            if (array.GetLowerBound(0) != 0)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_NonZeroLowerBound, ExceptionArgument.array);
            }

            int arrayLen = array.Length;
            if (index < 0 || index > arrayLen)
            {
                ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessOrEqualException();
            }

            if (arrayLen - index < _size)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Argument_InvalidOffLen);
            }

            int numToCopy = _size;
            if (numToCopy == 0) return;

            try
            {
                int firstPart = (_array.Length - _head < numToCopy) ? _array.Length - _head : numToCopy;
                Array.Copy(_array, _head, array, index, firstPart);
                numToCopy -= firstPart;

                if (numToCopy > 0)
                {
                    Array.Copy(_array, 0, array, index + _array.Length - _head, numToCopy);
                }
            }
            catch (ArrayTypeMismatchException)
            {
                ThrowHelper.ThrowArgumentException_Argument_IncompatibleArrayType();
            }
        }

        // Adds item to the tail of the queue.
        [Requires("@this.SpecCount < int.MaxValue")]
        [Ensures("@this.Items == Pal.Snoc(Pal.Old(@this.Items), item)")]
        public void Enqueue(T item)
        {
            if (_size == _array.Length)
            {
                Grow(_size + 1);
            }

            _array[_tail] = item;
            MoveNext(ref _tail);
            _size++;
            _version++;
        }

        // GetEnumerator returns an IEnumerator over this Queue.  This
        // Enumerator will support removing.
        [Ensures("ReferenceEquals(Result._queue, @this) && Result._version == @this.SpecVersion && Result._i == -1")]
        public Enumerator GetEnumerator() => new Enumerator(this);

        /// <internalonly/>
        [Ensures("Pal.Implies(@this.SpecCount != 0, Pal.Exists((Queue<T>.Enumerator e) => Pal.Boxes(Result, e) && " +
            "ReferenceEquals(e._queue, @this) && e._version == @this.SpecVersion && e._i == -1))")]
        IEnumerator<T> IEnumerable<T>.GetEnumerator() =>
            Count == 0 ? SZGenericArrayEnumerator<T>.Empty :
            GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<T>)this).GetEnumerator();

        // Removes the object at the head of the queue and returns it. If the queue
        // is empty, this method throws an
        // InvalidOperationException.
        [Throws(typeof(InvalidOperationException), "@this.SpecCount == 0")]
        [Ensures("0 < Pal.Old(@this.SpecCount)")]
        [Ensures("Pal.Same(Result, Pal.Old(@this.Items)[0])")]
        [Ensures("@this.Items == Pal.Slice(Pal.Old(@this.Items), 1, Pal.Old(@this.SpecCount))")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        public T Dequeue()
        {
            int head = _head;
            T[] array = _array;

            if (_size == 0)
            {
                ThrowForEmptyQueue();
            }

            T removed = array[head];
            if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
            {
                array[head] = default!;
            }
            MoveNext(ref _head);
            _size--;
            _version++;
            return removed;
        }

        [Ensures("Result == (0 < Pal.Old(@this.SpecCount))")]
        [Ensures("!Result || Pal.Same(result, Pal.Old(@this.Items)[0])")]
        [Ensures("@this.Items == (Result ? Pal.Slice(Pal.Old(@this.Items), 1, Pal.Old(@this.SpecCount)) : Pal.Old(@this.Items))")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        public bool TryDequeue([MaybeNullWhen(false)] out T result)
        {
            int head = _head;
            T[] array = _array;

            if (_size == 0)
            {
                result = default;
                return false;
            }

            result = array[head];
            if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
            {
                array[head] = default!;
            }
            MoveNext(ref _head);
            _size--;
            _version++;
            return true;
        }

        // Returns the object at the head of the queue. The object remains in the
        // queue. If the queue is empty, this method throws an
        // InvalidOperationException.
        [Throws(typeof(InvalidOperationException), "@this.SpecCount == 0")]
        [Ensures("0 < @this.SpecCount && Pal.Same(Result, @this.Items[0])")]
        public T Peek()
        {
            if (_size == 0)
            {
                ThrowForEmptyQueue();
            }

            return _array[_head];
        }

        [Ensures("Result == (0 < @this.SpecCount)")]
        [Ensures("!Result || Pal.Same(result, @this.Items[0])")]
        public bool TryPeek([MaybeNullWhen(false)] out T result)
        {
            if (_size == 0)
            {
                result = default;
                return false;
            }

            result = _array[_head];
            return true;
        }

        // Returns true if the queue contains at least one object equal to item.
        // Equality is determined using EqualityComparer<T>.Default.Equals().
        [Ensures("Result == (Pal.IndexOf(@this.Items, item) >= 0)")]
        public bool Contains(T item)
        {
            if (_size == 0)
            {
                return false;
            }

            if (_head < _tail)
            {
                return Array.IndexOf(_array, item, _head, _size) >= 0;
            }

            // We've wrapped around. Check both partitions, the least recently enqueued first.
            return
                Array.IndexOf(_array, item, _head, _array.Length - _head) >= 0 ||
                Array.IndexOf(_array, item, 0, _tail) >= 0;
        }

        // Iterates over the objects in the queue, returning an array of the
        // objects in the Queue, or an empty array if the queue is empty.
        // The order of elements in the array is first in to last in, the same
        // order produced by successive calls to Dequeue.
        [Ensures("Pal.Contents(Result) == @this.Items")]
        public T[] ToArray()
        {
            if (_size == 0)
            {
                return [];
            }

            T[] arr = new T[_size];

            if (_head < _tail)
            {
                Array.Copy(_array, _head, arr, 0, _size);
            }
            else
            {
                Array.Copy(_array, _head, arr, 0, _array.Length - _head);
                Array.Copy(_array, 0, arr, _array.Length - _head, _tail);
            }

            return arr;
        }

        // PRIVATE Grows or shrinks the buffer to hold capacity objects. Capacity
        // must be >= _size.
        [Requires("@this.SpecCount <= capacity")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity == capacity")]
        private void SetCapacity(int capacity)
        {
            Debug.Assert(capacity >= _size);
            T[] newarray = new T[capacity];
            if (_size > 0)
            {
                if (_head < _tail)
                {
                    Array.Copy(_array, _head, newarray, 0, _size);
                }
                else
                {
                    Array.Copy(_array, _head, newarray, 0, _array.Length - _head);
                    Array.Copy(_array, 0, newarray, _array.Length - _head, _tail);
                }
            }

            _array = newarray;
            _head = 0;
            _tail = (_size == capacity) ? 0 : _size;
            _version++;
        }

        // Increments the index wrapping it if necessary.
        [Requires("0 <= index && index < @this.SpecCapacity")]
        [Ensures("index == (Pal.Old(index) + 1 == @this.SpecCapacity ? 0 : Pal.Old(index) + 1)")]
        private void MoveNext(ref int index)
        {
            // It is tempting to use the remainder operator here but it is actually much slower
            // than a simple comparison and a rarely taken branch.
            // JIT produces better code than with ternary operator ?:
            int tmp = index + 1;
            if (tmp == _array.Length)
            {
                tmp = 0;
            }
            index = tmp;
        }

        [DoesNotReturn]
        [Requires("@this.SpecCount == 0")]
        [Throws(typeof(InvalidOperationException))]
        [Ensures("false")]
        private void ThrowForEmptyQueue()
        {
            Debug.Assert(_size == 0);
            throw new InvalidOperationException(SR.InvalidOperation_EmptyQueue);
        }

        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity) || @this.SpecCapacity == @this.SpecCount")]
        public void TrimExcess()
        {
            int threshold = (int)(_array.Length * 0.9);
            if (_size < threshold)
            {
                SetCapacity(_size);
            }
        }

        /// <summary>
        /// Sets the capacity of a <see cref="Queue{T}"/> object to the specified number of entries.
        /// </summary>
        /// <param name="capacity">The new capacity.</param>
        /// <exception cref="ArgumentOutOfRangeException">Passed capacity is lower than entries count.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0 || capacity < @this.SpecCount")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity == capacity")]
        public void TrimExcess(int capacity)
        {
            ArgumentOutOfRangeException.ThrowIfNegative(capacity);
            ArgumentOutOfRangeException.ThrowIfLessThan(capacity, _size);

            if (capacity == _array.Length)
                return;

            SetCapacity(capacity);
        }

        /// <summary>
        /// Ensures that the capacity of this Queue is at least the specified <paramref name="capacity"/>.
        /// </summary>
        /// <param name="capacity">The minimum capacity to ensure.</param>
        /// <returns>The new capacity of this queue.</returns>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity >= capacity")]
        [Ensures("Result == @this.SpecCapacity")]
        public int EnsureCapacity(int capacity)
        {
            ArgumentOutOfRangeException.ThrowIfNegative(capacity);

            if (_array.Length < capacity)
            {
                Grow(capacity);
            }

            return _array.Length;
        }

        [Wrapping]
        [Requires("@this.SpecCapacity < capacity")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity >= capacity")]
        private void Grow(int capacity)
        {
            Debug.Assert(_array.Length < capacity);

            const int GrowFactor = 2;
            const int MinimumGrow = 4;

            int newcapacity = GrowFactor * _array.Length;

            // Allow the list to grow to maximum possible capacity (~2G elements) before encountering overflow.
            // Note that this check works even when _items.Length overflowed thanks to the (uint) cast
            if ((uint)newcapacity > Array.MaxLength) newcapacity = Array.MaxLength;

            // Ensure minimum growth is respected.
            newcapacity = Math.Max(newcapacity, _array.Length + MinimumGrow);

            // If the computed capacity is still less than specified, set to the original argument.
            // Capacities exceeding Array.MaxLength will be surfaced as OutOfMemoryException by Array.Resize.
            if (newcapacity < capacity) newcapacity = capacity;

            SetCapacity(newcapacity);
        }

        // Implements an enumerator for a Queue.  The enumerator uses the
        // internal version number of the list to ensure that no modifications are
        // made to the list while an enumeration is in progress.
        public struct Enumerator : IEnumerator<T>,
            IEnumerator
        {
            private readonly Queue<T> _queue;
            private readonly int _version;
            private int _i;
            private T? _currentElement;

            [Ensures("ReferenceEquals(@this._queue, queue) && @this._version == queue.SpecVersion && @this._i == -1")]
            internal Enumerator(Queue<T> queue)
            {
                _queue = queue;
                _version = queue._version;
                _i = -1;
                _currentElement = default;
            }

            [Ensures("@this._i == -2")]
            public void Dispose()
            {
                _i = -2;
                _currentElement = default;
            }

            [Requires("@this._i < int.MaxValue")]
            [Requires("@this._queue.SpecHead + @this._queue.SpecCount <= int.MaxValue")]
            [Throws(typeof(InvalidOperationException), "@this._version != @this._queue.SpecVersion")]
            [Ensures("@this._version == @this._queue.SpecVersion")]
            [Ensures("Result == (0 <= Pal.Old(@this._i) + 1 && Pal.Old(@this._i) + 1 < @this._queue.SpecCount)")]
            [Ensures("Pal.Implies(Result, @this._i == Pal.Old(@this._i) + 1 && Pal.Same(@this._currentElement, @this._queue.Items[@this._i]))")]
            [Ensures("Pal.Implies(!Result, @this._i == -2)")]
            public bool MoveNext()
            {
                if (_version != _queue._version)
                {
                    ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                }

                Queue<T> q = _queue;
                int size = q._size;

                int offset = _i + 1;
                if ((uint)offset < (uint)size)
                {
                    _i = offset;

                    T[] array = q._array;
                    int index = q._head + offset;
                    if ((uint)index < (uint)array.Length)
                    {
                        _currentElement = array[index];
                    }
                    else
                    {
                        // The index has wrapped around the end of the array. Shift the index and then
                        // get the current element. It is tempting to dedup this dereferencing with that
                        // in the if block above, but the if block above avoids a bounds check for the
                        // accesses that are in that portion, whereas these still incur it.
                        index -= array.Length;
                        _currentElement = array[index];
                    }

                    return true;
                }

                _i = -2;
                _currentElement = default;
                return false;
            }

            [Ensures("Pal.Same(Result, @this._currentElement)")]
            public T Current => _currentElement!;

            [Ensures("Pal.Boxes(Result, @this._currentElement)")]
            object? IEnumerator.Current => Current;

            [Throws(typeof(InvalidOperationException), "@this._version != @this._queue.SpecVersion")]
            [Ensures("@this._version == @this._queue.SpecVersion && @this._i == -1")]
            void IEnumerator.Reset()
            {
                if (_version != _queue._version)
                {
                    ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                }

                _i = -1;
                _currentElement = default;
            }
        }
    }
}
