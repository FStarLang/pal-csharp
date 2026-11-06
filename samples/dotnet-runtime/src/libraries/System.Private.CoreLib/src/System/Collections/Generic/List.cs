// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using PalLang;

namespace System.Collections.Generic
{
    /// <summary>The abstract state of a <see cref="List{T}"/>: its elements and its capacity.</summary>
    [Spec]
    public struct ListModel<T>
    {
        public Seq<T> Items;
        public SpecInt Capacity;
        /// <summary>The whole backing store, of which <c>Items</c> is a prefix.</summary>
        public Seq<T> Store;
        /// <summary>The modification counter an enumerator checks.</summary>
        public SpecInt Version;
    }

    // Implements a variable-size List that uses an array of objects to store the
    // elements. A List has a capacity, which is the allocated length
    // of the internal array. As elements are added to a List, the capacity
    // of the List is automatically increased as required by reallocating the
    // internal array.
    //
    [DebuggerTypeProxy(typeof(ICollectionDebugView<>))]
    [DebuggerDisplay("Count = {Count}")]
    [Serializable]
    [TypeForwardedFrom("mscorlib, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    [Invariant("0 <= _size")]
    [Invariant("_size <= _items.Length")]
    public class List<T> : IList<T>, IList, IReadOnlyList<T>
    {
        private const int DefaultCapacity = 4;

        internal T[] _items; // Do not rename (binary serialization) [cDAC] [ComWrappers] : Contract depends on this exact name
        internal int _size; // Do not rename (binary serialization) [cDAC] [ComWrappers] : Contract depends on this exact name
        [Wrapping] internal int _version; // Do not rename (binary serialization)

#pragma warning disable CA1825, IDE0300 // avoid the extra generic instantiation for Array.Empty<T>()
        private static readonly T[] s_emptyArray = new T[0];
#pragma warning restore CA1825, IDE0300

        [Refine("Result.Items.Length <= Result.Capacity")]
        [Refine("Result.Store.Length == Result.Capacity")]
        [Model]
        private ListModel<T> Model => new ListModel<T>
        {
            Items = Pal.Slice(Pal.Contents(_items), 0, _size),
            Capacity = _items.Length,
            Store = Pal.Contents(_items),
            Version = _version,
        };

        /// <summary>The elements, in order.</summary>
        [Spec]
        public Seq<T> Items => Model.Items;

        [Spec]
        public SpecInt SpecCount => Model.Items.Length;

        [Spec]
        public SpecInt SpecCapacity => Model.Capacity;

        [Spec]
        public Seq<T> SpecStore => Model.Store;

        [Spec]
        public SpecInt SpecVersion => Model.Version;

        // Constructs a List. The list is initially empty and has a capacity
        // of zero. Upon adding the first element to the list the capacity is
        // increased to DefaultCapacity, and then increased in multiples of two
        // as required.
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == 0")]
        public List()
        {
            _items = s_emptyArray;
        }

        // Constructs a List with a given initial capacity. The list is
        // initially empty, but will have room for the given number of elements
        // before any reallocations are required.
        //
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == capacity")]
        public List(int capacity)
        {
            if (capacity < 0)
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.capacity, ExceptionResource.ArgumentOutOfRange_NeedNonNegNum);

            if (capacity == 0)
                _items = s_emptyArray;
            else
                _items = new T[capacity];
        }

        // Constructs a List, copying the contents of the given collection. The
        // size and capacity of the new list will both be equal to the size of the
        // given collection.
        //
        public List(IEnumerable<T> collection)
        {
            if (collection == null)
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.collection);

            if (collection is ICollection<T> c)
            {
                int count = c.Count;
                if (count == 0)
                {
                    _items = s_emptyArray;
                }
                else
                {
                    _items = new T[count];
                    c.CopyTo(_items, 0);
                    _size = count;
                }
            }
            else
            {
                _items = s_emptyArray;
                using (IEnumerator<T> en = collection.GetEnumerator())
                {
                    while (en.MoveNext())
                    {
                        Add(en.Current);
                    }
                }
            }
        }

        // Gets and sets the capacity of this list.  The capacity is the size of
        // the internal array used to hold items.  When set, the internal
        // array of the list is reallocated to the given capacity.
        //
        public int Capacity
        {
            [Ensures("Result == @this.SpecCapacity")]
            get => _items.Length;
            [Throws(typeof(ArgumentOutOfRangeException), "value < @this.SpecCount")]
            [Ensures("value >= Pal.Old(@this.SpecCount)")]
            [Ensures("@this.Items == Pal.Old(@this.Items)")]
            [Ensures("@this.SpecCapacity == value")]
            set
            {
                if (value < _size)
                {
                    ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.value, ExceptionResource.ArgumentOutOfRange_SmallCapacity);
                }

                if (value != _items.Length)
                {
                    if (value > 0)
                    {
                        T[] newItems = new T[value];
                        if (_size > 0)
                        {
                            Array.Copy(_items, newItems, _size);
                        }
                        _items = newItems;
                    }
                    else
                    {
                        _items = s_emptyArray;
                    }
                }
            }
        }

        // Read-only property describing how many elements are in the List.
        [Ensures("Result == @this.SpecCount")]
        public int Count => _size;

        bool IList.IsFixedSize => false;

        // Is this List read-only?
        bool ICollection<T>.IsReadOnly => false;

        bool IList.IsReadOnly => false;

        // Is this List synchronized (thread-safe)?
        bool ICollection.IsSynchronized => false;

        // Synchronization root for this object.
        object ICollection.SyncRoot => this;

        // Sets or Gets the element at the given index.
        public T this[int index]
        {
            [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
            [Ensures("0 <= index && index < @this.SpecCount && Pal.Same(Result, @this.Items[index])")]
            get
            {
                // Following trick can reduce the range check by one
                if ((uint)index >= (uint)_size)
                {
                    ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessException();
                }
                return _items[index];
            }

            [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
            [Ensures("0 <= index && index < Pal.Old(@this.SpecCount)")]
            [Ensures("@this.Items == Pal.SetAt(Pal.Old(@this.Items), index, value)")]
            [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
            set
            {
                if ((uint)index >= (uint)_size)
                {
                    ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessException();
                }
                _items[index] = value;
                _version++;
            }
        }

        private static bool IsCompatibleObject(object? value)
        {
            // Non-null values are fine.  Only accept nulls if T is a class or Nullable<U>.
            // Note that default(T) is not equal to null for value types except when T is Nullable<U>.
            return (value is T) || (value == null && default(T) == null);
        }

        object? IList.this[int index]
        {
            get => this[index];
            set
            {
                ThrowHelper.IfNullAndNullsAreIllegalThenThrow<T>(value, ExceptionArgument.value);

                try
                {
                    this[index] = (T)value!;
                }
                catch (InvalidCastException)
                {
                    ThrowHelper.ThrowWrongValueTypeArgumentException(value, typeof(T));
                }
            }
        }

        // Adds the given object to the end of this list. The size of the list is
        // increased by one. If required, the capacity of the list is doubled
        // before adding the new element.
        //
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        [Requires("@this.SpecCount < int.MaxValue")]
        [Ensures("@this.Items == Pal.Snoc(Pal.Old(@this.Items), item)")]
        public void Add(T item)
        {
            _version++;
            T[] array = _items;
            int size = _size;
            if ((uint)size < (uint)array.Length)
            {
                _size = size + 1;
                array[size] = item;
            }
            else
            {
                AddWithResize(item);
            }
        }

        // Non-inline from List.Add to improve its code quality as uncommon path
        [MethodImpl(MethodImplOptions.NoInlining)]
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

        int IList.Add(object? item)
        {
            ThrowHelper.IfNullAndNullsAreIllegalThenThrow<T>(item, ExceptionArgument.item);

            try
            {
                Add((T)item!);
            }
            catch (InvalidCastException)
            {
                ThrowHelper.ThrowWrongValueTypeArgumentException(item, typeof(T));
            }

            return Count - 1;
        }

        // Adds the elements of the given collection to the end of this list. If
        // required, the capacity of the list is increased to twice the previous
        // capacity or the new size, whichever is larger.
        //
        public void AddRange(IEnumerable<T> collection)
        {
            if (collection == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.collection);
            }

            if (collection is ICollection<T> c)
            {
                int count = c.Count;
                if (count > 0)
                {
                    if (_items.Length - _size < count)
                    {
                        Grow(checked(_size + count));
                    }

                    c.CopyTo(_items, _size);
                    _size += count;
                    _version++;
                }
            }
            else
            {
                using (IEnumerator<T> en = collection.GetEnumerator())
                {
                    while (en.MoveNext())
                    {
                        Add(en.Current);
                    }
                }
            }
        }

        public ReadOnlyCollection<T> AsReadOnly()
            => new ReadOnlyCollection<T>(this);

        // Searches a section of the list for a given element using a binary search
        // algorithm. Elements of the list are compared to the search value using
        // the given IComparer interface. If comparer is null, elements of
        // the list are compared to the search value using the IComparable
        // interface, which in that case must be implemented by all elements of the
        // list and the given search value. This method assumes that the given
        // section of the list is already sorted; if this is not the case, the
        // result will be incorrect.
        //
        // The method returns the index of the given value in the list. If the
        // list does not contain the given value, the method returns a negative
        // integer. The bitwise complement operator (~) can be applied to a
        // negative result to produce the index of the first element (if any) that
        // is larger than the given search value. This is also the index at which
        // the search value should be inserted into the list in order for the list
        // to remain sorted.
        //
        // The method uses the Array.BinarySearch method to perform the
        // search.
        //
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || count < 0")]
        [Throws(typeof(ArgumentException), "index >= 0 && count >= 0 && @this.SpecCount - index < count")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("Result == Pal.BinarySearch(comparer ?? Comparer<T>.Default, @this.Items, index, count, item)")]
        public int BinarySearch(int index, int count, T item, IComparer<T>? comparer)
        {
            if (index < 0)
                ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
            if (count < 0)
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.count, ExceptionResource.ArgumentOutOfRange_NeedNonNegNum);
            if (_size - index < count)
                ThrowHelper.ThrowArgumentException(ExceptionResource.Argument_InvalidOffLen);

            return Array.BinarySearch(_items, index, count, item, comparer);
        }

        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("Result == Pal.BinarySearch(Comparer<T>.Default, @this.Items, 0, @this.SpecCount, item)")]
        public int BinarySearch(T item)
            => BinarySearch(0, Count, item, null);

        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("Result == Pal.BinarySearch(comparer ?? Comparer<T>.Default, @this.Items, 0, @this.SpecCount, item)")]
        public int BinarySearch(T item, IComparer<T>? comparer)
            => BinarySearch(0, Count, item, comparer);

        // Clears the contents of List.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        public void Clear()
        {
            _version++;
            if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
            {
                int size = _size;
                _size = 0;
                if (size > 0)
                {
                    Array.Clear(_items, 0, size); // Clear the elements so that the gc can reclaim the references.
                }
            }
            else
            {
                _size = 0;
            }
        }

        // Contains returns true if the specified element is in the List.
        // It does a linear, O(n) search.  Equality is determined by calling
        // EqualityComparer<T>.Default.Equals().
        //
        [Ensures("Result == (Pal.IndexOf(@this.Items, item) >= 0)")]
        public bool Contains(T item)
        {
            // PERF: IndexOf calls Array.IndexOf, which internally
            // calls EqualityComparer<T>.Default.IndexOf, which
            // is specialized for different types. This
            // boosts performance since instead of making a
            // virtual method call each iteration of the loop,
            // via EqualityComparer<T>.Default.Equals, we
            // only make one virtual call to EqualityComparer.IndexOf.

            return _size != 0 && IndexOf(item) >= 0;
        }

        bool IList.Contains(object? item)
        {
            if (IsCompatibleObject(item))
            {
                return Contains((T)item!);
            }
            return false;
        }

        public List<TOutput> ConvertAll<TOutput>(Converter<T, TOutput> converter)
        {
            if (converter == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.converter);
            }

            List<TOutput> list = new List<TOutput>(_size);
            for (int i = 0; i < _size; i++)
            {
                list._items[i] = converter(_items[i]);
            }
            list._size = _size;
            return list;
        }

        // Copies this List into array, which must be of a
        // compatible array type.
        [Requires("@this.SpecCount <= Pal.Contents(array).Length")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), 0, @this.SpecCount, @this.Items)")]
        public void CopyTo(T[] array)
            => CopyTo(array, 0);

        // Copies this List into array, which must be of a
        // compatible array type.
        void ICollection.CopyTo(Array array, int arrayIndex)
        {
            if ((array != null) && (array.Rank != 1))
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_RankMultiDimNotSupported);
            }

            try
            {
                // Array.Copy will check for NULL.
                Array.Copy(_items, 0, array!, arrayIndex, _size);
            }
            catch (ArrayTypeMismatchException)
            {
                ThrowHelper.ThrowArgumentException_Argument_IncompatibleArrayType();
            }
        }

        // Copies a section of this list to the given array at the given index.
        //
        // The method uses the Array.Copy method to copy the elements.
        //
        [Requires("index >= 0 && count >= 0 && arrayIndex >= 0")]
        [Requires("arrayIndex + count <= Pal.Contents(array).Length")]
        [Throws(typeof(ArgumentException), "@this.SpecCount - index < count")]
        [Ensures("index + count <= @this.SpecCount")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), arrayIndex, arrayIndex + count, Pal.Slice(@this.Items, index, index + count))")]
        public void CopyTo(int index, T[] array, int arrayIndex, int count)
        {
            if (_size - index < count)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Argument_InvalidOffLen);
            }

            // Delegate rest of error checking to Array.Copy.
            Array.Copy(_items, index, array, arrayIndex, count);
        }

        [Requires("arrayIndex >= 0 && arrayIndex + @this.SpecCount <= Pal.Contents(array).Length")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), arrayIndex, arrayIndex + @this.SpecCount, @this.Items)")]
        public void CopyTo(T[] array, int arrayIndex)
        {
            // Delegate rest of error checking to Array.Copy.
            Array.Copy(_items, 0, array, arrayIndex, _size);
        }

        /// <summary>
        /// Ensures that the capacity of this list is at least the specified <paramref name="capacity"/>.
        /// If the current capacity of the list is less than specified <paramref name="capacity"/>,
        /// the capacity is increased to at least <paramref name="capacity"/>.
        /// </summary>
        /// <param name="capacity">The minimum capacity to ensure.</param>
        /// <returns>The new capacity of this list.</returns>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity >= capacity")]
        [Ensures("Result == @this.SpecCapacity")]
        public int EnsureCapacity(int capacity)
        {
            if (capacity < 0)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.capacity, ExceptionResource.ArgumentOutOfRange_NeedNonNegNum);
            }
            if (_items.Length < capacity)
            {
                Grow(capacity);
            }

            return _items.Length;
        }

        /// <summary>
        /// Increase the capacity of this list to at least the specified <paramref name="capacity"/>.
        /// </summary>
        /// <param name="capacity">The minimum capacity to ensure.</param>
        [Requires("@this.SpecCapacity < capacity")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity >= capacity")]
        internal void Grow(int capacity)
        {
            Capacity = GetNewCapacity(capacity);
        }

        /// <summary>
        /// Enlarge this list so it may contain at least <paramref name="insertionCount"/> more elements
        /// And copy data to their after-insertion positions.
        /// This method is specifically for insertion, as it avoids 1 extra array copy.
        /// You should only call this method when Count + insertionCount > Capacity.
        /// </summary>
        /// <param name="indexToInsert">Index of the first insertion.</param>
        /// <param name="insertionCount">How many elements will be inserted.</param>
        [Requires("0 <= indexToInsert && indexToInsert <= @this.SpecCount")]
        [Requires("insertionCount > 0 && @this.SpecCount + insertionCount <= int.MaxValue")]
        [Requires("@this.SpecCapacity - @this.SpecCount < insertionCount")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCapacity >= @this.SpecCount + insertionCount")]
        [Ensures("Pal.Slice(@this.SpecStore, 0, indexToInsert) == Pal.Slice(Pal.Old(@this.Items), 0, indexToInsert)")]
        [Ensures("Pal.Slice(@this.SpecStore, indexToInsert + insertionCount, @this.SpecCount + insertionCount) == " +
                 "Pal.Slice(Pal.Old(@this.Items), indexToInsert, @this.SpecCount)")]
        internal void GrowForInsertion(int indexToInsert, int insertionCount = 1)
        {
            Debug.Assert(insertionCount > 0);

            int requiredCapacity = checked(_size + insertionCount);
            int newCapacity = GetNewCapacity(requiredCapacity);

            // Inline and adapt logic from set_Capacity

            T[] newItems = new T[newCapacity];
            if (indexToInsert != 0)
            {
                Array.Copy(_items, newItems, length: indexToInsert);
            }

            if (_size != indexToInsert)
            {
                Array.Copy(_items, indexToInsert, newItems, indexToInsert + insertionCount, _size - indexToInsert);
            }

            _items = newItems;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        [Wrapping]
        [Requires("@this.SpecCapacity < capacity")]
        [Ensures("Result >= capacity")]
        private int GetNewCapacity(int capacity)
        {
            Debug.Assert(_items.Length < capacity);

            int newCapacity = _items.Length == 0 ? DefaultCapacity : 2 * _items.Length;

            // Allow the list to grow to maximum possible capacity (~2G elements) before encountering overflow.
            // Note that this check works even when _items.Length overflowed thanks to the (uint) cast
            if ((uint)newCapacity > Array.MaxLength) newCapacity = Array.MaxLength;

            // If the computed capacity is still less than specified, set to the original argument.
            // Capacities exceeding Array.MaxLength will be surfaced as OutOfMemoryException by Array.Resize.
            if (newCapacity < capacity) newCapacity = capacity;

            return newCapacity;
        }

        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("Result == (Pal.FindIndex(@this.Items, match) != -1)")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public bool Exists(Predicate<T> match)
            => FindIndex(match) != -1;

        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("Pal.FindIndex(@this.Items, match) == -1 ? Pal.Same(Result, default(T)) : " +
                 "Pal.Same(Result, @this.Items[Pal.FindIndex(@this.Items, match)])")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public T? Find(Predicate<T> match)
        {
            if (match == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.match);
            }

            for (int i = 0; i < _size; i++)
            {
                Pal.Invariant(0 <= i && i <= _size && _size <= _items.Length);
                Pal.Invariant(Pal.Forall((SpecInt k) =>
                    Pal.Implies(0 <= k && k < i, !match(Pal.Contents(_items)[k]))));
                Pal.Invariant(Pal.Implies(Pal.Returned(),
                    i < _size && match(Pal.Contents(_items)[i]) && Pal.Same(Pal.ReturnValue<T>(), Pal.Contents(_items)[i])));
                if (match(_items[i]))
                {
                    return _items[i];
                }
            }
            return default;
        }

        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("Result.Items == Pal.FindAll(@this.Items, match)")]
        public List<T> FindAll(Predicate<T> match)
        {
            if (match == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.match);
            }

            List<T> list = new List<T>();
            for (int i = 0; i < _size; i++)
            {
                Pal.Invariant(0 <= i && i <= _size && _size <= _items.Length);
                Pal.Invariant(Pal.Slice(Pal.Contents(_items), 0, _size) == Pal.Old(this.Items));
                Pal.Invariant(list.Items == Pal.FindAll(Pal.Slice(Pal.Old(this.Items), 0, i), match));
                Pal.Invariant(list.SpecCount <= i);
                if (match(_items[i]))
                {
                    list.Add(_items[i]);
                }
            }
            return list;
        }

        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("Result == Pal.FindIndex(@this.Items, match)")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public int FindIndex(Predicate<T> match)
            => FindIndex(0, _size, match);

        // `_size - startIndex` is computed before the range check, and wraps when
        // `startIndex` is very negative (the callee then throws); pal-csharp's arithmetic
        // does not wrap, so the precondition excludes it.
        [Requires("@this.SpecCount - startIndex <= int.MaxValue")]
        [Throws(typeof(ArgumentOutOfRangeException), "startIndex < 0 || startIndex > @this.SpecCount")]
        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("0 <= startIndex && startIndex <= @this.SpecCount")]
        [Ensures("Result == Pal.FindIndex(@this.Items, match, startIndex, @this.SpecCount - startIndex)")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public int FindIndex(int startIndex, Predicate<T> match)
            => FindIndex(startIndex, _size - startIndex, match);

        [Throws(typeof(ArgumentOutOfRangeException),
            "startIndex < 0 || startIndex > @this.SpecCount || count < 0 || startIndex > @this.SpecCount - count")]
        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("0 <= startIndex && 0 <= count && startIndex + count <= @this.SpecCount")]
        [Ensures("Result == Pal.FindIndex(@this.Items, match, startIndex, count)")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public int FindIndex(int startIndex, int count, Predicate<T> match)
        {
            if ((uint)startIndex > (uint)_size)
            {
                ThrowHelper.ThrowStartIndexArgumentOutOfRange_ArgumentOutOfRange_IndexMustBeLessOrEqual();
            }

            if (count < 0 || startIndex > _size - count)
            {
                ThrowHelper.ThrowCountArgumentOutOfRange_ArgumentOutOfRange_Count();
            }

            if (match == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.match);
            }

            int endIndex = startIndex + count;
            for (int i = startIndex; i < endIndex; i++)
            {
                Pal.Invariant(startIndex <= i && i <= endIndex && endIndex <= _size && _size <= _items.Length);
                Pal.Invariant(Pal.Forall((SpecInt k) =>
                    Pal.Implies(startIndex <= k && k < i, !match(Pal.Contents(_items)[k]))));
                Pal.Invariant(Pal.Implies(Pal.Returned(),
                    Pal.ReturnValue<int>() == i && i < endIndex && match(Pal.Contents(_items)[i])));
                if (match(_items[i])) return i;
            }
            return -1;
        }

        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("Pal.FindLastIndex(@this.Items, match) == -1 ? Pal.Same(Result, default(T)) : " +
                 "Pal.Same(Result, @this.Items[Pal.FindLastIndex(@this.Items, match)])")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public T? FindLast(Predicate<T> match)
        {
            if (match == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.match);
            }

            for (int i = _size - 1; i >= 0; i--)
            {
                Pal.Invariant(-1 <= i && i < _size && _size <= _items.Length);
                Pal.Invariant(Pal.Forall((SpecInt k) =>
                    Pal.Implies(i < k && k < _size, !match(Pal.Contents(_items)[k]))));
                Pal.Invariant(Pal.Implies(Pal.Returned(),
                    0 <= i && match(Pal.Contents(_items)[i]) && Pal.Same(Pal.ReturnValue<T>(), Pal.Contents(_items)[i])));
                if (match(_items[i]))
                {
                    return _items[i];
                }
            }
            return default;
        }

        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("Result == Pal.FindLastIndex(@this.Items, match)")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public int FindLastIndex(Predicate<T> match)
            => FindLastIndex(_size - 1, _size, match);

        // `startIndex + 1` wraps at `int.MaxValue` (the callee then throws for the negative
        // count); pal-csharp's arithmetic does not wrap, so the precondition excludes it.
        [Requires("startIndex < int.MaxValue")]
        [Throws(typeof(ArgumentNullException), "match == null")]
        [Throws(typeof(ArgumentOutOfRangeException),
            "@this.SpecCount == 0 ? startIndex != -1 : startIndex < 0 || startIndex >= @this.SpecCount")]
        [Ensures("@this.SpecCount == 0 ? startIndex == -1 : 0 <= startIndex && startIndex < @this.SpecCount")]
        [Ensures("Result == Pal.FindLastIndex(@this.Items, match, startIndex, startIndex + 1)")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public int FindLastIndex(int startIndex, Predicate<T> match)
            => FindLastIndex(startIndex, startIndex + 1, match);

        [Throws(typeof(ArgumentNullException), "match == null")]
        [Throws(typeof(ArgumentOutOfRangeException),
            "(@this.SpecCount == 0 ? startIndex != -1 : startIndex < 0 || startIndex >= @this.SpecCount) || " +
            "count < 0 || startIndex - count + 1 < 0")]
        [Ensures("@this.SpecCount == 0 ? startIndex == -1 : 0 <= startIndex && startIndex < @this.SpecCount")]
        [Ensures("0 <= count && startIndex - count + 1 >= 0")]
        [Ensures("Result == Pal.FindLastIndex(@this.Items, match, startIndex, count)")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public int FindLastIndex(int startIndex, int count, Predicate<T> match)
        {
            if (match == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.match);
            }

            if (_size == 0)
            {
                // Special case for 0 length List
                if (startIndex != -1)
                {
                    ThrowHelper.ThrowStartIndexArgumentOutOfRange_ArgumentOutOfRange_IndexMustBeLess();
                }
            }
            else
            {
                // Make sure we're not out of range
                if ((uint)startIndex >= (uint)_size)
                {
                    ThrowHelper.ThrowStartIndexArgumentOutOfRange_ArgumentOutOfRange_IndexMustBeLess();
                }
            }

            // 2nd have of this also catches when startIndex == MAXINT, so MAXINT - 0 + 1 == -1, which is < 0.
            if (count < 0 || startIndex - count + 1 < 0)
            {
                ThrowHelper.ThrowCountArgumentOutOfRange_ArgumentOutOfRange_Count();
            }

            int endIndex = startIndex - count;
            for (int i = startIndex; i > endIndex; i--)
            {
                Pal.Invariant(-1 <= endIndex && endIndex <= i && i <= startIndex && startIndex < _size && _size <= _items.Length);
                Pal.Invariant(Pal.Forall((SpecInt k) =>
                    Pal.Implies(i < k && k <= startIndex, !match(Pal.Contents(_items)[k]))));
                Pal.Invariant(Pal.Implies(Pal.Returned(),
                    Pal.ReturnValue<int>() == i && endIndex < i && match(Pal.Contents(_items)[i])));
                if (match(_items[i]))
                {
                    return i;
                }
            }
            return -1;
        }

        [Throws(typeof(ArgumentNullException), "action == null")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public void ForEach(Action<T> action)
        {
            if (action == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.action);
            }

            int version = _version;

            for (int i = 0; i < _size; i++)
            {
                Pal.Invariant(0 <= i && i <= _size && _size <= _items.Length);
                Pal.Invariant(version == _version);
                if (version != _version)
                {
                    break;
                }
                action(_items[i]);
            }

            if (version != _version)
                ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
        }

        // Returns an enumerator for this list with the given
        // permission for removal of elements. If modifications made to the list
        // while an enumeration is in progress, the MoveNext and
        // GetObject methods of the enumerator will throw an exception.
        //
        [Ensures("ReferenceEquals(Result._list, @this) && Result._version == @this.SpecVersion && Result._index == 0")]
        public Enumerator GetEnumerator() => new Enumerator(this);

        [Ensures("Pal.Implies(@this.SpecCount != 0, Pal.Exists((List<T>.Enumerator e) => Pal.Boxes(Result, e) && " +
            "ReferenceEquals(e._list, @this) && e._version == @this.SpecVersion && e._index == 0))")]
        IEnumerator<T> IEnumerable<T>.GetEnumerator() =>
            Count == 0 ? SZGenericArrayEnumerator<T>.Empty :
            GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<T>)this).GetEnumerator();

        public List<T> GetRange(int index, int count)
        {
            if (index < 0)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
            }

            if (count < 0)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.count, ExceptionResource.ArgumentOutOfRange_NeedNonNegNum);
            }

            if (_size - index < count)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Argument_InvalidOffLen);
            }

            List<T> list = new List<T>(count);
            Array.Copy(_items, index, list._items, 0, count);
            list._size = count;
            return list;
        }

        /// <summary>
        /// Creates a shallow copy of a range of elements in the source <see cref="List{T}" />.
        /// </summary>
        /// <param name="start">The zero-based <see cref="List{T}" /> index at which the range starts.</param>
        /// <param name="length">The length of the range.</param>
        /// <returns>A shallow copy of a range of elements in the source <see cref="List{T}" />.</returns>
        /// <exception cref="ArgumentOutOfRangeException">
        /// <paramref name="start" /> is less than 0.
        /// -or-
        /// <paramref name="length" /> is less than 0.
        /// </exception>
        /// <exception cref="ArgumentException"><paramref name="start" /> and <paramref name="length" /> do not denote a valid range of elements in the <see cref="List{T}" />.</exception>
        public List<T> Slice(int start, int length) => GetRange(start, length);

        // Returns the index of the first occurrence of a given value in a range of
        // this list. The list is searched forwards from beginning to end.
        // The elements of the list are compared to the given value using the
        // Object.Equals method.
        //
        // This method uses the Array.IndexOf method to perform the
        // search.
        //
        [Ensures("Result == Pal.IndexOf(@this.Items, item)")]
        public int IndexOf(T item)
            => Array.IndexOf(_items, item, 0, _size);

        int IList.IndexOf(object? item)
        {
            if (IsCompatibleObject(item))
            {
                return IndexOf((T)item!);
            }
            return -1;
        }

        // Returns the index of the first occurrence of a given value in a range of
        // this list. The list is searched forwards, starting at index
        // index and ending at count number of elements. The
        // elements of the list are compared to the given value using the
        // Object.Equals method.
        //
        // This method uses the Array.IndexOf method to perform the
        // search.
        //
        [Requires("index >= 0")]
        [Throws(typeof(ArgumentOutOfRangeException), "index > @this.SpecCount")]
        [Ensures("index <= @this.SpecCount")]
        [Ensures("Result == Pal.IndexOf(@this.Items, item, index, @this.SpecCount - index)")]
        public int IndexOf(T item, int index)
        {
            if (index > _size)
                ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessOrEqualException();
            return Array.IndexOf(_items, item, index, _size - index);
        }

        // Returns the index of the first occurrence of a given value in a range of
        // this list. The list is searched forwards, starting at index
        // index and upto count number of elements. The
        // elements of the list are compared to the given value using the
        // Object.Equals method.
        //
        // This method uses the Array.IndexOf method to perform the
        // search.
        //
        [Requires("index >= 0")]
        [Throws(typeof(ArgumentOutOfRangeException), "index > @this.SpecCount || count < 0 || index > @this.SpecCount - count")]
        [Ensures("0 <= count && index + count <= @this.SpecCount")]
        [Ensures("Result == Pal.IndexOf(@this.Items, item, index, count)")]
        public int IndexOf(T item, int index, int count)
        {
            if (index > _size)
                ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessOrEqualException();

            if (count < 0 || index > _size - count)
                ThrowHelper.ThrowCountArgumentOutOfRange_ArgumentOutOfRange_Count();

            return Array.IndexOf(_items, item, index, count);
        }

        // Inserts an element into this list at a given index. The size of the list
        // is increased by one. If required, the capacity of the list is doubled
        // before inserting the new element.
        //
        [Requires("@this.SpecCount < int.MaxValue")]
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index > @this.SpecCount")]
        [Ensures("0 <= index && index <= Pal.Old(@this.SpecCount)")]
        [Ensures("@this.Items == Pal.Concat(Pal.Snoc(Pal.Slice(Pal.Old(@this.Items), 0, index), item), " +
                 "Pal.Slice(Pal.Old(@this.Items), index, Pal.Old(@this.SpecCount)))")]
        public void Insert(int index, T item)
        {
            // Note that insertions at the end are legal.
            if ((uint)index > (uint)_size)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.index, ExceptionResource.ArgumentOutOfRange_ListInsert);
            }
            if (_size == _items.Length)
            {
                GrowForInsertion(index, 1);
            }
            else if (index < _size)
            {
                Array.Copy(_items, index, _items, index + 1, _size - index);
            }
            _items[index] = item;
            _size++;
            _version++;
        }

        void IList.Insert(int index, object? item)
        {
            ThrowHelper.IfNullAndNullsAreIllegalThenThrow<T>(item, ExceptionArgument.item);

            try
            {
                Insert(index, (T)item!);
            }
            catch (InvalidCastException)
            {
                ThrowHelper.ThrowWrongValueTypeArgumentException(item, typeof(T));
            }
        }

        // Inserts the elements of the given collection at a given index. If
        // required, the capacity of the list is increased to twice the previous
        // capacity or the new size, whichever is larger.  Ranges may be added
        // to the end of the list by setting index to the List's size.
        //
        public void InsertRange(int index, IEnumerable<T> collection)
        {
            if (collection == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.collection);
            }

            if ((uint)index > (uint)_size)
            {
                ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessOrEqualException();
            }

            if (collection is ICollection<T> c)
            {
                int count = c.Count;
                if (count > 0)
                {
                    if (_items.Length - _size < count)
                    {
                        GrowForInsertion(index, count);
                    }
                    else if (index < _size)
                    {
                        Array.Copy(_items, index, _items, index + count, _size - index);
                    }

                    // If we're inserting a List into itself, we want to be able to deal with that.
                    if (this == c)
                    {
                        // Copy first part of _items to insert location
                        Array.Copy(_items, 0, _items, index, index);
                        // Copy last part of _items back to inserted location
                        Array.Copy(_items, index + count, _items, index * 2, _size - index);
                    }
                    else
                    {
                        c.CopyTo(_items, index);
                    }
                    _size += count;
                    _version++;
                }
            }
            else
            {
                using (IEnumerator<T> en = collection.GetEnumerator())
                {
                    while (en.MoveNext())
                    {
                        Insert(index++, en.Current);
                    }
                }
            }
        }

        // Returns the index of the last occurrence of a given value in a range of
        // this list. The list is searched backwards, starting at the end
        // and ending at the first element in the list. The elements of the list
        // are compared to the given value using the Object.Equals method.
        //
        // This method uses the Array.LastIndexOf method to perform the
        // search.
        //
        [Ensures("Result == Pal.LastIndexOf(@this.Items, item)")]
        public int LastIndexOf(T item)
        {
            if (_size == 0)
            {  // Special case for empty list
                return -1;
            }
            else
            {
                return LastIndexOf(item, _size - 1, _size);
            }
        }

        // Returns the index of the last occurrence of a given value in a range of
        // this list. The list is searched backwards, starting at index
        // index and ending at the first element in the list. The
        // elements of the list are compared to the given value using the
        // Object.Equals method.
        //
        // This method uses the Array.LastIndexOf method to perform the
        // search.
        //
        // On an empty list a negative index is not an error: the search is skipped.
        [Throws(typeof(ArgumentOutOfRangeException), "index >= @this.SpecCount || (@this.SpecCount != 0 && index < 0)")]
        [Ensures("@this.SpecCount == 0 ? index < 0 && Result == -1 : " +
                 "0 <= index && index < @this.SpecCount && Result == Pal.LastIndexOf(@this.Items, item, index, index + 1)")]
        public int LastIndexOf(T item, int index)
        {
            if (index >= _size)
                ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessException();
            return LastIndexOf(item, index, index + 1);
        }

        // Returns the index of the last occurrence of a given value in a range of
        // this list. The list is searched backwards, starting at index
        // index and upto count elements. The elements of
        // the list are compared to the given value using the Object.Equals
        // method.
        //
        // This method uses the Array.LastIndexOf method to perform the
        // search.
        //
        [Throws(typeof(ArgumentOutOfRangeException),
            "@this.SpecCount != 0 && (index < 0 || count < 0 || index >= @this.SpecCount || count > index + 1)")]
        [Ensures("@this.SpecCount == 0 || (0 <= index && index < @this.SpecCount && 0 <= count && count <= index + 1)")]
        [Ensures("@this.SpecCount == 0 ? Result == -1 : Result == Pal.LastIndexOf(@this.Items, item, index, count)")]
        public int LastIndexOf(T item, int index, int count)
        {
            if ((Count != 0) && (index < 0))
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
            }

            if ((Count != 0) && (count < 0))
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.count, ExceptionResource.ArgumentOutOfRange_NeedNonNegNum);
            }

            if (_size == 0)
            {  // Special case for empty list
                return -1;
            }

            if (index >= _size)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.index, ExceptionResource.ArgumentOutOfRange_BiggerThanCollection);
            }

            if (count > index + 1)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.count, ExceptionResource.ArgumentOutOfRange_BiggerThanCollection);
            }

            return Array.LastIndexOf(_items, item, index, count);
        }

        // Removes the first occurrence of the given element, if found.
        // The size of the list is decreased by one if successful.
        [Ensures("Result == (Pal.IndexOf(Pal.Old(@this.Items), item) >= 0)")]
        [Ensures("Result ? @this.Items == Pal.Concat(Pal.Slice(Pal.Old(@this.Items), 0, Pal.IndexOf(Pal.Old(@this.Items), item)), " +
                 "Pal.Slice(Pal.Old(@this.Items), Pal.IndexOf(Pal.Old(@this.Items), item) + 1, Pal.Old(@this.SpecCount))) " +
                 ": @this.Items == Pal.Old(@this.Items)")]
        public bool Remove(T item)
        {
            int index = IndexOf(item);
            if (index >= 0)
            {
                RemoveAt(index);
                return true;
            }

            return false;
        }

        void IList.Remove(object? item)
        {
            if (IsCompatibleObject(item))
            {
                Remove((T)item!);
            }
        }

        // This method removes all items which matches the predicate.
        // The complexity is O(n).
        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("@this.Items == Pal.RemoveAll(Pal.Old(@this.Items), match)")]
        [Ensures("Result == Pal.Old(@this.SpecCount) - @this.SpecCount")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        public int RemoveAll(Predicate<T> match)
        {
            if (match == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.match);
            }

            int freeIndex = 0;   // the first free slot in items array

            // Find the first item which needs to be removed.
            while (freeIndex < _size && !match(_items[freeIndex]))
            {
                Pal.Invariant(0 <= freeIndex && freeIndex <= _size && _size <= _items.Length);
                Pal.Invariant(Pal.Slice(Pal.Contents(_items), 0, _size) == Pal.Old(this.Items));
                Pal.Invariant(Pal.Forall((SpecInt k) =>
                    Pal.Implies(0 <= k && k < freeIndex, !match(Pal.Contents(_items)[k]))));
                Pal.Decreases(_size - freeIndex);
                freeIndex++;
            }
            if (freeIndex >= _size) return 0;

            int current = freeIndex + 1;
            while (current < _size)
            {
                Pal.Invariant(0 <= freeIndex && freeIndex < current && current <= _size && _size <= _items.Length);
                Pal.Invariant(_size == Pal.Old(this.SpecCount) && _items.Length == Pal.Old(this.SpecCapacity));
                Pal.Invariant(Pal.Slice(Pal.Contents(_items), 0, freeIndex) ==
                    Pal.RemoveAll(Pal.Slice(Pal.Old(this.Items), 0, current), match));
                Pal.Invariant(Pal.Forall((SpecInt k) =>
                    Pal.Implies(current <= k && k < _size, Pal.Same(Pal.Contents(_items)[k], Pal.Old(this.Items)[k]))));
                Pal.Decreases(_size - freeIndex + (current < _size ? 1 : 0));
                // Find the first item which needs to be kept.
                while (current < _size && match(_items[current]))
                {
                    Pal.Invariant(0 <= freeIndex && freeIndex < current && current <= _size && _size <= _items.Length);
                    Pal.Invariant(_size == Pal.Old(this.SpecCount) && _items.Length == Pal.Old(this.SpecCapacity));
                    Pal.Invariant(Pal.Slice(Pal.Contents(_items), 0, freeIndex) ==
                        Pal.RemoveAll(Pal.Slice(Pal.Old(this.Items), 0, current), match));
                    Pal.Invariant(Pal.Forall((SpecInt k) =>
                        Pal.Implies(current <= k && k < _size, Pal.Same(Pal.Contents(_items)[k], Pal.Old(this.Items)[k]))));
                    Pal.Decreases(_size - current);
                    current++;
                }

                if (current < _size)
                {
                    // copy item to the free slot.
                    _items[freeIndex++] = _items[current++];
                    Pal.Assert(!match(Pal.Old(this.Items)[current - 1]));
                    Pal.Assert(Pal.Same(Pal.Contents(_items)[freeIndex - 1], Pal.Old(this.Items)[current - 1]));
                    Pal.Assert(Pal.Slice(Pal.Contents(_items), 0, freeIndex - 1) ==
                        Pal.RemoveAll(Pal.Slice(Pal.Old(this.Items), 0, current - 1), match));
                    Pal.Assert(Pal.Slice(Pal.Contents(_items), 0, freeIndex) ==
                        Pal.RemoveAll(Pal.Slice(Pal.Old(this.Items), 0, current), match));
                }
            }

            if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
            {
                Array.Clear(_items, freeIndex, _size - freeIndex); // Clear the elements so that the gc can reclaim the references.
            }

            int result = _size - freeIndex;
            _size = freeIndex;
            _version++;
            return result;
        }

        // Removes the element at the given index. The size of the list is
        // decreased by one.
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
        [Ensures("0 <= index && index < Pal.Old(@this.SpecCount)")]
        [Ensures("@this.Items == Pal.Concat(Pal.Slice(Pal.Old(@this.Items), 0, index), " +
                 "Pal.Slice(Pal.Old(@this.Items), index + 1, Pal.Old(@this.SpecCount)))")]
        public void RemoveAt(int index)
        {
            if ((uint)index >= (uint)_size)
            {
                ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessException();
            }
            _size--;
            if (index < _size)
            {
                Array.Copy(_items, index + 1, _items, index, _size - index);
            }
            if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
            {
                _items[_size] = default!;
            }
            _version++;
        }

        // Removes a range of elements from this list.
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || count < 0")]
        [Throws(typeof(ArgumentException), "index >= 0 && count >= 0 && @this.SpecCount - index < count")]
        [Ensures("0 <= index && 0 <= count && index + count <= Pal.Old(@this.SpecCount)")]
        [Ensures("@this.Items == Pal.Concat(Pal.Slice(Pal.Old(@this.Items), 0, index), " +
                 "Pal.Slice(Pal.Old(@this.Items), index + count, Pal.Old(@this.SpecCount)))")]
        public void RemoveRange(int index, int count)
        {
            if (index < 0)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
            }

            if (count < 0)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.count, ExceptionResource.ArgumentOutOfRange_NeedNonNegNum);
            }

            if (_size - index < count)
                ThrowHelper.ThrowArgumentException(ExceptionResource.Argument_InvalidOffLen);

            if (count > 0)
            {
                _size -= count;
                if (index < _size)
                {
                    Array.Copy(_items, index + count, _items, index, _size - index);
                }

                _version++;
                if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
                {
                    Array.Clear(_items, _size, count);
                }
            }
        }

        // Reverses the elements in this list.
        [Ensures("@this.Items == Pal.Reverse(Pal.Old(@this.Items))")]
        public void Reverse()
            => Reverse(0, Count);

        // Reverses the elements in a range of this list. Following a call to this
        // method, an element in the range given by index and count
        // which was previously located at index i will now be located at
        // index index + (index + count - i - 1).
        //
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || count < 0")]
        [Throws(typeof(ArgumentException), "index >= 0 && count >= 0 && @this.SpecCount - index < count")]
        [Ensures("0 <= index && 0 <= count && index + count <= Pal.Old(@this.SpecCount)")]
        [Ensures("@this.Items == Pal.Concat(Pal.Concat(Pal.Slice(Pal.Old(@this.Items), 0, index), " +
                 "Pal.Reverse(Pal.Slice(Pal.Old(@this.Items), index, index + count))), " +
                 "Pal.Slice(Pal.Old(@this.Items), index + count, Pal.Old(@this.SpecCount)))")]
        public void Reverse(int index, int count)
        {
            if (index < 0)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
            }

            if (count < 0)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.count, ExceptionResource.ArgumentOutOfRange_NeedNonNegNum);
            }

            if (_size - index < count)
                ThrowHelper.ThrowArgumentException(ExceptionResource.Argument_InvalidOffLen);

            if (count > 1)
            {
                Array.Reverse(_items, index, count);
            }
            _version++;
        }

        // Sorts the elements in this list.  Uses the default comparer and
        // Array.Sort.
        [Ensures("Pal.SortedRange(Pal.Old(@this.Items), @this.Items, 0, Pal.Old(@this.SpecCount), null)")]
        public void Sort()
            => Sort(0, Count, null);

        // Sorts the elements in this list.  Uses Array.Sort with the
        // provided comparer.
        [Ensures("Pal.SortedRange(Pal.Old(@this.Items), @this.Items, 0, Pal.Old(@this.SpecCount), comparer)")]
        public void Sort(IComparer<T>? comparer)
            => Sort(0, Count, comparer);

        // Sorts the elements in a section of this list. The sort compares the
        // elements to each other using the given IComparer interface. If
        // comparer is null, the elements are compared to each other using
        // the IComparable interface, which in that case must be implemented by all
        // elements of the list.
        //
        // This method uses the Array.Sort method to sort the elements.
        //
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || count < 0")]
        [Throws(typeof(ArgumentException), "index >= 0 && count >= 0 && @this.SpecCount - index < count")]
        [Ensures("0 <= index && 0 <= count && index + count <= Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("Pal.SortedRange(Pal.Old(@this.Items), @this.Items, index, count, comparer)")]
        public void Sort(int index, int count, IComparer<T>? comparer)
        {
            if (index < 0)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
            }

            if (count < 0)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.count, ExceptionResource.ArgumentOutOfRange_NeedNonNegNum);
            }

            if (_size - index < count)
                ThrowHelper.ThrowArgumentException(ExceptionResource.Argument_InvalidOffLen);

            if (count > 1)
            {
                Array.Sort(_items, index, count, comparer);
            }
            _version++;
        }

        public void Sort(Comparison<T> comparison)
        {
            if (comparison == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.comparison);
            }

            if (_size > 1)
            {
                ArraySortHelper<T>.Sort(new Span<T>(_items, 0, _size), comparison);
            }
            _version++;
        }

        // ToArray returns an array containing the contents of the List.
        // This requires copying the List, which is an O(n) operation.
        [Ensures("Pal.Contents(Result) == @this.Items")]
        public T[] ToArray()
        {
            if (_size == 0)
            {
                return s_emptyArray;
            }

            T[] array = new T[_size];
            Array.Copy(_items, array, _size);
            return array;
        }

        // Sets the capacity of this list to the size of the list. This method can
        // be used to minimize a list's memory overhead once it is known that no
        // new elements will be added to the list. To completely clear a list and
        // release all memory referenced by the list, execute the following
        // statements:
        //
        // list.Clear();
        // list.TrimExcess();
        //
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.SpecCapacity <= Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity) || @this.SpecCapacity == @this.SpecCount")]
        public void TrimExcess()
        {
            int threshold = (int)(((double)_items.Length) * 0.9);
            if (_size < threshold)
            {
                Capacity = _size;
            }
        }

        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("Result == Pal.TrueForAll(@this.Items, match)")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        public bool TrueForAll(Predicate<T> match)
        {
            if (match == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.match);
            }

            for (int i = 0; i < _size; i++)
            {
                Pal.Invariant(0 <= i && i <= _size && _size <= _items.Length);
                Pal.Invariant(Pal.Forall((SpecInt k) =>
                    Pal.Implies(0 <= k && k < i, match(Pal.Contents(_items)[k]))));
                Pal.Invariant(Pal.Implies(Pal.Returned(),
                    !Pal.ReturnValue<bool>() && i < _size && !match(Pal.Contents(_items)[i])));
                if (!match(_items[i]))
                {
                    return false;
                }
            }
            return true;
        }

        public struct Enumerator : IEnumerator<T>, IEnumerator
        {
            private readonly List<T> _list;
            private readonly int _version;

            private int _index;
            private T? _current;

            [Ensures("ReferenceEquals(@this._list, list) && @this._version == list.SpecVersion && @this._index == 0")]
            internal Enumerator(List<T> list)
            {
                _list = list;
                _version = list._version;
            }

            [Ensures("true")]
            public void Dispose()
            {
            }

            [Throws(typeof(InvalidOperationException), "@this._version != @this._list.SpecVersion")]
            [Ensures("@this._version == @this._list.SpecVersion")]
            [Ensures("Result == (0 <= Pal.Old(@this._index) && Pal.Old(@this._index) < @this._list.SpecCount)")]
            [Ensures("Pal.Implies(Result, @this._index == Pal.Old(@this._index) + 1 && Pal.Same(@this._current, @this._list.Items[Pal.Old(@this._index)]))")]
            [Ensures("Pal.Implies(!Result, @this._index == -1)")]
            public bool MoveNext()
            {
                List<T> localList = _list;

                if (_version != _list._version)
                {
                    ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                }

                if ((uint)_index < (uint)localList._size)
                {
                    _current = localList._items[_index];
                    _index++;
                    return true;
                }

                _current = default;
                _index = -1;
                return false;
            }

            [Ensures("Pal.Same(Result, @this._current)")]
            public T Current => _current!;

            [Throws(typeof(InvalidOperationException), "@this._index <= 0")]
            [Ensures("Pal.Boxes(Result, @this._current)")]
            object? IEnumerator.Current
            {
                get
                {
                    if (_index <= 0)
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen();
                    }

                    return _current;
                }
            }

            [Throws(typeof(InvalidOperationException), "@this._version != @this._list.SpecVersion")]
            [Ensures("@this._version == @this._list.SpecVersion && @this._index == 0")]
            void IEnumerator.Reset()
            {
                if (_version != _list._version)
                {
                    ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                }

                _index = 0;
                _current = default;
            }
        }
    }
}
