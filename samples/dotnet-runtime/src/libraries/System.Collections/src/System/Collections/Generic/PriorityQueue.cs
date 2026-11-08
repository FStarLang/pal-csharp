// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using PalLang;

namespace System.Collections.Generic
{
    /// <summary>
    /// The abstract state of a <see cref="PriorityQueue{TElement, TPriority}"/>: its nodes in
    /// backing array, how much of it is in use (the nodes, in heap order), and the comparer
    /// it orders priorities by.
    /// </summary>
    [Spec]
    public struct PriorityQueueModel<TElement, TPriority>
    {
        public Seq<(TElement Element, TPriority Priority)> Store;
        public SpecInt Size;
        public IComparer<TPriority>? Order;
        /// <summary>The modification counter an enumerator checks.</summary>
        public SpecInt Version;
    }

    /// <summary>
    ///  Represents a min priority queue.
    /// </summary>
    /// <typeparam name="TElement">Specifies the type of elements in the queue.</typeparam>
    /// <typeparam name="TPriority">Specifies the type of priority associated with enqueued elements.</typeparam>
    /// <remarks>
    ///  Implements an array-backed quaternary min-heap. Each element is enqueued with an associated priority
    ///  that determines the dequeue order: elements with the lowest priority get dequeued first.
    /// </remarks>
    [DebuggerDisplay("Count = {Count}")]
    [DebuggerTypeProxy(typeof(PriorityQueueDebugView<,>))]
    [Invariant("0 <= _size")]
    [Invariant("_size <= _nodes.Length")]
    public class PriorityQueue<TElement, TPriority>
    {
        /// <summary>
        /// Represents an implicit heap-ordered complete d-ary tree, stored as an array.
        /// </summary>
        private (TElement Element, TPriority Priority)[] _nodes;

        /// <summary>
        /// Custom comparer used to order the heap.
        /// </summary>
        private readonly IComparer<TPriority>? _comparer;

        /// <summary>
        /// The number of nodes in the heap.
        /// </summary>
        private int _size;

        /// <summary>
        /// Version updated on mutation to help validate enumerators operate on a consistent state.
        /// </summary>
        [Wrapping]
        private int _version;

        /// <summary>
        /// Specifies the arity of the d-ary heap, which here is quaternary.
        /// It is assumed that this value is a power of 2.
        /// </summary>
        private const int Arity = 4;

        /// <summary>
        /// The binary logarithm of <see cref="Arity" />.
        /// </summary>
        private const int Log2Arity = 2;

        [Refine("0 <= Result.Size && Result.Size <= Result.Store.Length")]
        [Model]
        private PriorityQueueModel<TElement, TPriority> Model => new PriorityQueueModel<TElement, TPriority>
        {
            Store = Pal.Contents(_nodes),
            Size = _size,
            Order = _comparer,
            Version = _version,
        };

        /// <summary>The whole backing array, whose first <see cref="SpecCount"/> nodes are <see cref="Items"/>.</summary>
        [Spec]
        public Seq<(TElement Element, TPriority Priority)> Store => Model.Store;

        /// <summary>The nodes, in heap order: <c>Items[(i - 1) / 4]</c> is node <c>i</c>'s parent.</summary>
        [Spec]
        public Seq<(TElement Element, TPriority Priority)> Items => Pal.Slice(Model.Store, 0, Model.Size);

        [Spec]
        public SpecInt SpecCount => Model.Size;

        [Spec]
        public SpecInt SpecVersion => Model.Version;

        [Spec]
        public SpecInt SpecCapacity => Model.Store.Length;

        /// <summary>The comparer as given; <c>null</c> stands for <c>Comparer&lt;TPriority&gt;.Default</c>.</summary>
        [Spec]
        public IComparer<TPriority>? Order => Model.Order;

#if DEBUG
        static PriorityQueue()
        {
            Debug.Assert(Log2Arity > 0 && Math.Pow(2, Log2Arity) == Arity);
        }
#endif

        /// <summary>
        ///  Initializes a new instance of the <see cref="PriorityQueue{TElement, TPriority}"/> class.
        /// </summary>
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == 0")]
        [Ensures("(@this.Order ?? Comparer<TPriority>.Default) == Comparer<TPriority>.Default")]
        public PriorityQueue()
        {
            _nodes = Array.Empty<(TElement, TPriority)>();
            _comparer = InitializeComparer(null);
        }

        /// <summary>
        ///  Initializes a new instance of the <see cref="PriorityQueue{TElement, TPriority}"/> class
        ///  with the specified initial capacity.
        /// </summary>
        /// <param name="initialCapacity">Initial capacity to allocate in the underlying heap array.</param>
        /// <exception cref="ArgumentOutOfRangeException">
        ///  The specified <paramref name="initialCapacity"/> was negative.
        /// </exception>
        [Throws(typeof(ArgumentOutOfRangeException), "initialCapacity < 0")]
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == initialCapacity")]
        [Ensures("(@this.Order ?? Comparer<TPriority>.Default) == Comparer<TPriority>.Default")]
        public PriorityQueue(int initialCapacity)
            : this(initialCapacity, comparer: null)
        {
        }

        /// <summary>
        ///  Initializes a new instance of the <see cref="PriorityQueue{TElement, TPriority}"/> class
        ///  with the specified custom priority comparer.
        /// </summary>
        /// <param name="comparer">
        ///  Custom comparer dictating the ordering of elements.
        ///  Uses <see cref="Comparer{T}.Default" /> if the argument is <see langword="null"/>.
        /// </param>
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == 0")]
        [Ensures("(@this.Order ?? Comparer<TPriority>.Default) == (comparer ?? Comparer<TPriority>.Default)")]
        public PriorityQueue(IComparer<TPriority>? comparer)
        {
            _nodes = Array.Empty<(TElement, TPriority)>();
            _comparer = InitializeComparer(comparer);
        }

        /// <summary>
        ///  Initializes a new instance of the <see cref="PriorityQueue{TElement, TPriority}"/> class
        ///  with the specified initial capacity and custom priority comparer.
        /// </summary>
        /// <param name="initialCapacity">Initial capacity to allocate in the underlying heap array.</param>
        /// <param name="comparer">
        ///  Custom comparer dictating the ordering of elements.
        ///  Uses <see cref="Comparer{T}.Default" /> if the argument is <see langword="null"/>.
        /// </param>
        /// <exception cref="ArgumentOutOfRangeException">
        ///  The specified <paramref name="initialCapacity"/> was negative.
        /// </exception>
        [Throws(typeof(ArgumentOutOfRangeException), "initialCapacity < 0")]
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == initialCapacity")]
        [Ensures("(@this.Order ?? Comparer<TPriority>.Default) == (comparer ?? Comparer<TPriority>.Default)")]
        public PriorityQueue(int initialCapacity, IComparer<TPriority>? comparer)
        {
            ArgumentOutOfRangeException.ThrowIfNegative(initialCapacity);

            _nodes = new (TElement, TPriority)[initialCapacity];
            _comparer = InitializeComparer(comparer);
        }

        /// <summary>
        ///  Initializes a new instance of the <see cref="PriorityQueue{TElement, TPriority}"/> class
        ///  that is populated with the specified elements and priorities.
        /// </summary>
        /// <param name="items">The pairs of elements and priorities with which to populate the queue.</param>
        /// <exception cref="ArgumentNullException">
        ///  The specified <paramref name="items"/> argument was <see langword="null"/>.
        /// </exception>
        /// <remarks>
        ///  Constructs the heap using a heapify operation,
        ///  which is generally faster than enqueuing individual elements sequentially.
        /// </remarks>
        public PriorityQueue(IEnumerable<(TElement Element, TPriority Priority)> items)
            : this(items, comparer: null)
        {
        }

        /// <summary>
        ///  Initializes a new instance of the <see cref="PriorityQueue{TElement, TPriority}"/> class
        ///  that is populated with the specified elements and priorities,
        ///  and with the specified custom priority comparer.
        /// </summary>
        /// <param name="items">The pairs of elements and priorities with which to populate the queue.</param>
        /// <param name="comparer">
        ///  Custom comparer dictating the ordering of elements.
        ///  Uses <see cref="Comparer{T}.Default" /> if the argument is <see langword="null"/>.
        /// </param>
        /// <exception cref="ArgumentNullException">
        ///  The specified <paramref name="items"/> argument was <see langword="null"/>.
        /// </exception>
        /// <remarks>
        ///  Constructs the heap using a heapify operation,
        ///  which is generally faster than enqueuing individual elements sequentially.
        /// </remarks>
        public PriorityQueue(IEnumerable<(TElement Element, TPriority Priority)> items, IComparer<TPriority>? comparer)
        {
            ArgumentNullException.ThrowIfNull(items);

            _nodes = EnumerableHelpers.ToArray(items, out _size);
            _comparer = InitializeComparer(comparer);

            if (_size > 1)
            {
                Heapify();
            }
        }

        /// <summary>
        ///  Gets the number of elements contained in the <see cref="PriorityQueue{TElement, TPriority}"/>.
        /// </summary>
        [Ensures("Result == @this.SpecCount")]
        public int Count => _size;

        /// <summary>
        ///  Gets the total numbers of elements the queue's backing storage can hold without resizing.
        /// </summary>
        [Ensures("Result == @this.SpecCapacity")]
        public int Capacity => _nodes.Length;

        /// <summary>
        ///  Gets the priority comparer used by the <see cref="PriorityQueue{TElement, TPriority}"/>.
        /// </summary>
        [Ensures("Result == (@this.Order ?? Comparer<TPriority>.Default)")]
        public IComparer<TPriority> Comparer => _comparer ?? Comparer<TPriority>.Default;

        /// <summary>
        ///  Gets a collection that enumerates the elements of the queue in an unordered manner.
        /// </summary>
        /// <remarks>
        ///  The enumeration does not order items by priority, since that would require N * log(N) time and N space.
        ///  Items are instead enumerated following the internal array heap layout.
        /// </remarks>
        [Ensures("ReferenceEquals(Result._queue, @this)")]
        public UnorderedItemsCollection UnorderedItems => field ??= new UnorderedItemsCollection(this);

        /// <summary>
        ///  Adds the specified element with associated priority to the <see cref="PriorityQueue{TElement, TPriority}"/>.
        /// </summary>
        /// <param name="element">The element to add to the <see cref="PriorityQueue{TElement, TPriority}"/>.</param>
        /// <param name="priority">The priority with which to associate the new element.</param>
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        // Unreachable in practice: an array is never longer than Array.MaxLength.
        [Requires("@this.SpecCount < 2147483647")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Permutation(Pal.Snoc(Pal.Old(@this.Items), (element, priority)), @this.Items)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        public void Enqueue(TElement element, TPriority priority)
        {
            // Virtually add the node at the end of the underlying array.
            // Note that the node being enqueued does not need to be physically placed
            // there at this point, as such an assignment would be redundant.

            int currentSize = _size;
            _version++;

            if (_nodes.Length == currentSize)
            {
                Grow(currentSize + 1);
            }

            _size = currentSize + 1;
            HeapUpInit(Pal.Contents(_nodes), _size, (element, priority), _comparer);

            if (_comparer == null)
            {
                MoveUpDefaultComparer((element, priority), currentSize);
            }
            else
            {
                MoveUpCustomComparer((element, priority), currentSize);
            }
        }

        /// <summary>
        ///  Returns the minimal element from the <see cref="PriorityQueue{TElement, TPriority}"/> without removing it.
        /// </summary>
        /// <exception cref="InvalidOperationException">The <see cref="PriorityQueue{TElement, TPriority}"/> is empty.</exception>
        /// <returns>The minimal element of the <see cref="PriorityQueue{TElement, TPriority}"/>.</returns>
        [Throws(typeof(InvalidOperationException), "@this.SpecCount == 0")]
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("@this.SpecCount > 0 && Pal.Same(Result, @this.Items[0].Element)")]
        [Ensures("@this.SpecCount > 0 && Pal.HeapMin(@this.Items, @this.Items[0], @this.Order)")]
        public TElement Peek()
        {
            if (_size == 0)
            {
                throw new InvalidOperationException(SR.InvalidOperation_EmptyQueue);
            }

            return _nodes[0].Element;
        }

        /// <summary>
        ///  Removes and returns the minimal element from the <see cref="PriorityQueue{TElement, TPriority}"/>.
        /// </summary>
        /// <exception cref="InvalidOperationException">The queue is empty.</exception>
        /// <returns>The minimal element of the <see cref="PriorityQueue{TElement, TPriority}"/>.</returns>
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        // (nodeIndex << 2) + 1 wraps for nodeIndex >= 2^29; see the spec findings.
        [Requires("@this.SpecCount <= 536870912")]
        [Throws(typeof(InvalidOperationException), "@this.SpecCount == 0")]
        [Ensures("Pal.Old(@this.SpecCount) > 0 && Pal.Same(Result, Pal.Old(@this.Items)[0].Element)")]
        [Ensures("Pal.Old(@this.SpecCount) > 0 && Pal.HeapMin(Pal.Old(@this.Items), Pal.Old(@this.Items)[0], @this.Order)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) - 1")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Old(@this.SpecCount) > 0 && Pal.Permutation(Pal.Old(@this.Items), Pal.Snoc(@this.Items, Pal.Old(@this.Items)[0]))")]
        public TElement Dequeue()
        {
            if (_size == 0)
            {
                throw new InvalidOperationException(SR.InvalidOperation_EmptyQueue);
            }

            TElement element = _nodes[0].Element;
            RemoveRootNode();
            return element;
        }

        /// <summary>
        ///  Removes the minimal element and then immediately adds the specified element with associated priority to the <see cref="PriorityQueue{TElement, TPriority}"/>,
        /// </summary>
        /// <param name="element">The element to add to the <see cref="PriorityQueue{TElement, TPriority}"/>.</param>
        /// <param name="priority">The priority with which to associate the new element.</param>
        /// <exception cref="InvalidOperationException">The queue is empty.</exception>
        /// <returns>The minimal element removed before performing the enqueue operation.</returns>
        /// <remarks>
        ///  Implements an extract-then-insert heap operation that is generally more efficient
        ///  than sequencing Dequeue and Enqueue operations: in the worst case scenario only one
        ///  shift-down operation is required.
        /// </remarks>
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        // (nodeIndex << 2) + 1 wraps for nodeIndex >= 2^29; see the spec findings.
        [Requires("@this.SpecCount <= 536870912")]
        [Throws(typeof(InvalidOperationException), "@this.SpecCount == 0")]
        [Ensures("Pal.Old(@this.SpecCount) > 0 && Pal.Same(Result, Pal.Old(@this.Items)[0].Element)")]
        [Ensures("Pal.Old(@this.SpecCount) > 0 && Pal.HeapMin(Pal.Old(@this.Items), Pal.Old(@this.Items)[0], @this.Order)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Old(@this.SpecCount) > 0 && Pal.Permutation(Pal.SetAt(Pal.Old(@this.Items), 0, (element, priority)), @this.Items)")]
        public TElement DequeueEnqueue(TElement element, TPriority priority)
        {
            if (_size == 0)
            {
                throw new InvalidOperationException(SR.InvalidOperation_EmptyQueue);
            }

            (TElement Element, TPriority Priority) root = _nodes[0];

            if (_comparer == null)
            {
                if (Comparer<TPriority>.Default.Compare(priority, root.Priority) > 0)
                {
                    HeapDownInit(Pal.Contents(_nodes), _size, (element, priority), _comparer);
                    MoveDownDefaultComparer((element, priority), 0);
                }
                else
                {
                    HeapReplaceRoot(Pal.Contents(_nodes), _size, (element, priority), _comparer);
                    _nodes[0] = (element, priority);
                }
            }
            else
            {
                if (_comparer.Compare(priority, root.Priority) > 0)
                {
                    HeapDownInit(Pal.Contents(_nodes), _size, (element, priority), _comparer);
                    MoveDownCustomComparer((element, priority), 0);
                }
                else
                {
                    HeapReplaceRoot(Pal.Contents(_nodes), _size, (element, priority), _comparer);
                    _nodes[0] = (element, priority);
                }
            }

            _version++;
            return root.Element;
        }

        /// <summary>
        ///  Removes the minimal element from the <see cref="PriorityQueue{TElement, TPriority}"/>,
        ///  and copies it to the <paramref name="element"/> parameter,
        ///  and its associated priority to the <paramref name="priority"/> parameter.
        /// </summary>
        /// <param name="element">The removed element.</param>
        /// <param name="priority">The priority associated with the removed element.</param>
        /// <returns>
        ///  <see langword="true"/> if the element is successfully removed;
        ///  <see langword="false"/> if the <see cref="PriorityQueue{TElement, TPriority}"/> is empty.
        /// </returns>
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        // (nodeIndex << 2) + 1 wraps for nodeIndex >= 2^29; see the spec findings.
        [Requires("@this.SpecCount <= 536870912")]
        [Ensures("Result == (Pal.Old(@this.SpecCount) > 0)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Implies(!Result, @this.SpecCount == 0)")]
        [Ensures("Pal.Implies(Result, Pal.Same(element, Pal.Old(@this.Items)[0].Element) && Pal.Same(priority, Pal.Old(@this.Items)[0].Priority))")]
        [Ensures("Pal.Implies(Result, Pal.HeapMin(Pal.Old(@this.Items), Pal.Old(@this.Items)[0], @this.Order))")]
        [Ensures("Pal.Implies(Result, @this.SpecCount == Pal.Old(@this.SpecCount) - 1 && Pal.Permutation(Pal.Old(@this.Items), Pal.Snoc(@this.Items, Pal.Old(@this.Items)[0])))")]
        public bool TryDequeue([MaybeNullWhen(false)] out TElement element, [MaybeNullWhen(false)] out TPriority priority)
        {
            if (_size != 0)
            {
                (element, priority) = _nodes[0];
                RemoveRootNode();
                return true;
            }

            element = default;
            priority = default;
            return false;
        }

        /// <summary>
        ///  Returns a value that indicates whether there is a minimal element in the <see cref="PriorityQueue{TElement, TPriority}"/>,
        ///  and if one is present, copies it to the <paramref name="element"/> parameter,
        ///  and its associated priority to the <paramref name="priority"/> parameter.
        ///  The element is not removed from the <see cref="PriorityQueue{TElement, TPriority}"/>.
        /// </summary>
        /// <param name="element">The minimal element in the queue.</param>
        /// <param name="priority">The priority associated with the minimal element.</param>
        /// <returns>
        ///  <see langword="true"/> if there is a minimal element;
        ///  <see langword="false"/> if the <see cref="PriorityQueue{TElement, TPriority}"/> is empty.
        /// </returns>
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Result == (@this.SpecCount > 0)")]
        [Ensures("Pal.Implies(Result, Pal.Same(element, @this.Items[0].Element) && Pal.Same(priority, @this.Items[0].Priority))")]
        [Ensures("Pal.Implies(Result, Pal.HeapMin(@this.Items, @this.Items[0], @this.Order))")]
        public bool TryPeek([MaybeNullWhen(false)] out TElement element, [MaybeNullWhen(false)] out TPriority priority)
        {
            if (_size != 0)
            {
                (element, priority) = _nodes[0];
                return true;
            }

            element = default;
            priority = default;
            return false;
        }

        /// <summary>
        ///  Adds the specified element with associated priority to the <see cref="PriorityQueue{TElement, TPriority}"/>,
        ///  and immediately removes the minimal element, returning the result.
        /// </summary>
        /// <param name="element">The element to add to the <see cref="PriorityQueue{TElement, TPriority}"/>.</param>
        /// <param name="priority">The priority with which to associate the new element.</param>
        /// <returns>The minimal element removed after the enqueue operation.</returns>
        /// <remarks>
        ///  Implements an insert-then-extract heap operation that is generally more efficient
        ///  than sequencing Enqueue and Dequeue operations: in the worst case scenario only one
        ///  shift-down operation is required.
        /// </remarks>
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        // (nodeIndex << 2) + 1 wraps for nodeIndex >= 2^29; see the spec findings.
        [Requires("@this.SpecCount <= 536870912")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Implies(Pal.Old(@this.SpecCount) > 0 && Pal.Compare(@this.Order ?? Comparer<TPriority>.Default, priority, Pal.Old(@this.Items)[0].Priority) > 0, Pal.Same(Result, Pal.Old(@this.Items)[0].Element) && Pal.Permutation(Pal.SetAt(Pal.Old(@this.Items), 0, (element, priority)), @this.Items))")]
        [Ensures("Pal.Implies(!(Pal.Old(@this.SpecCount) > 0 && Pal.Compare(@this.Order ?? Comparer<TPriority>.Default, priority, Pal.Old(@this.Items)[0].Priority) > 0), Pal.Same(Result, element) && @this.Items == Pal.Old(@this.Items))")]
        public TElement EnqueueDequeue(TElement element, TPriority priority)
        {
            if (_size != 0)
            {
                (TElement Element, TPriority Priority) root = _nodes[0];

                if (_comparer == null)
                {
                    if (Comparer<TPriority>.Default.Compare(priority, root.Priority) > 0)
                    {
                        HeapDownInit(Pal.Contents(_nodes), _size, (element, priority), _comparer);
                        MoveDownDefaultComparer((element, priority), 0);
                        _version++;
                        return root.Element;
                    }
                }
                else
                {
                    if (_comparer.Compare(priority, root.Priority) > 0)
                    {
                        HeapDownInit(Pal.Contents(_nodes), _size, (element, priority), _comparer);
                        MoveDownCustomComparer((element, priority), 0);
                        _version++;
                        return root.Element;
                    }
                }
            }

            return element;
        }

        /// <summary>
        ///  Enqueues a sequence of element/priority pairs to the <see cref="PriorityQueue{TElement, TPriority}"/>.
        /// </summary>
        /// <param name="items">The pairs of elements and priorities to add to the queue.</param>
        /// <exception cref="ArgumentNullException">
        ///  The specified <paramref name="items"/> argument was <see langword="null"/>.
        /// </exception>
        public void EnqueueRange(IEnumerable<(TElement Element, TPriority Priority)> items)
        {
            ArgumentNullException.ThrowIfNull(items);

            int count = 0;
            var collection = items as ICollection<(TElement Element, TPriority Priority)>;
            if (collection is not null && (count = collection.Count) > _nodes.Length - _size)
            {
                Grow(checked(_size + count));
            }

            if (_size == 0)
            {
                // build using Heapify() if the queue is empty.

                if (collection is not null)
                {
                    collection.CopyTo(_nodes, 0);
                    _size = count;
                }
                else
                {
                    int i = 0;
                    (TElement, TPriority)[] nodes = _nodes;
                    foreach ((TElement element, TPriority priority) in items)
                    {
                        if (nodes.Length == i)
                        {
                            Grow(i + 1);
                            nodes = _nodes;
                        }

                        nodes[i++] = (element, priority);
                    }

                    _size = i;
                }

                _version++;

                if (_size > 1)
                {
                    Heapify();
                }
            }
            else
            {
                foreach ((TElement element, TPriority priority) in items)
                {
                    Enqueue(element, priority);
                }
            }
        }

        /// <summary>
        ///  Enqueues a sequence of elements pairs to the <see cref="PriorityQueue{TElement, TPriority}"/>,
        ///  all associated with the specified priority.
        /// </summary>
        /// <param name="elements">The elements to add to the queue.</param>
        /// <param name="priority">The priority to associate with the new elements.</param>
        /// <exception cref="ArgumentNullException">
        ///  The specified <paramref name="elements"/> argument was <see langword="null"/>.
        /// </exception>
        public void EnqueueRange(IEnumerable<TElement> elements, TPriority priority)
        {
            ArgumentNullException.ThrowIfNull(elements);

            int count;
            if (elements is ICollection<TElement> collection &&
                (count = collection.Count) > _nodes.Length - _size)
            {
                Grow(checked(_size + count));
            }

            if (_size == 0)
            {
                // If the queue is empty just append the elements since they all have the same priority.

                int i = 0;
                (TElement, TPriority)[] nodes = _nodes;
                foreach (TElement element in elements)
                {
                    if (nodes.Length == i)
                    {
                        Grow(i + 1);
                        nodes = _nodes;
                    }

                    nodes[i++] = (element, priority);
                }

                _size = i;
                _version++;
            }
            else
            {
                foreach (TElement element in elements)
                {
                    Enqueue(element, priority);
                }
            }
        }

        /// <summary>
        /// Removes the first occurrence that equals the specified parameter.
        /// </summary>
        /// <param name="element">The element to try to remove.</param>
        /// <param name="removedElement">The actual element that got removed from the queue.</param>
        /// <param name="priority">The priority value associated with the removed element.</param>
        /// <param name="equalityComparer">The equality comparer governing element equality.</param>
        /// <returns><see langword="true"/> if matching entry was found and removed, <see langword="false"/> otherwise.</returns>
        /// <remarks>
        /// The method performs a linear-time scan of every element in the heap, removing the first value found to match the <paramref name="element"/> parameter.
        /// In case of duplicate entries, what entry does get removed is non-deterministic and does not take priority into account.
        ///
        /// If no <paramref name="equalityComparer"/> is specified, <see cref="EqualityComparer{TElement}.Default"/> will be used instead.
        /// </remarks>
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        // (nodeIndex << 2) + 1 wraps for nodeIndex >= 2^29; see the spec findings.
        [Requires("@this.SpecCount <= 536870912")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Result == !PriorityQueue<TElement, TPriority>.NoMatch(equalityComparer, element, Pal.Old(@this.Items), Pal.Old(@this.SpecCount))")]
        [Ensures("Pal.Implies(!Result, @this.SpecCount == Pal.Old(@this.SpecCount) && @this.Items == Pal.Old(@this.Items))")]
        [Ensures("Pal.Implies(Result, @this.SpecCount == Pal.Old(@this.SpecCount) - 1 && PriorityQueue<TElement, TPriority>.ElemEq(equalityComparer, element, removedElement) && Pal.Permutation(Pal.Old(@this.Items), Pal.Snoc(@this.Items, (removedElement, priority))))")]
        public bool Remove(
            TElement element,
            [MaybeNullWhen(false)] out TElement removedElement,
            [MaybeNullWhen(false)] out TPriority priority,
            IEqualityComparer<TElement>? equalityComparer = null)
        {
            int index = FindIndex(element, equalityComparer);
            if (index < 0)
            {
                removedElement = default;
                priority = default;
                return false;
            }

            (TElement Element, TPriority Priority)[] nodes = _nodes;
            (removedElement, priority) = nodes[index];
            int newSize = --_size;

            if (index < newSize)
            {
                // We're removing an element from the middle of the heap.
                // Pop the last element in the collection and sift from the removed index.
                (TElement Element, TPriority Priority) lastNode = nodes[newSize];
                HeapRemoveInit(Pal.Contents(_nodes), newSize, index, _comparer);

                if (_comparer == null)
                {
                    if (Comparer<TPriority>.Default.Compare(lastNode.Priority, priority) < 0)
                    {
                        MoveUpDefaultComparer(lastNode, index);
                    }
                    else
                    {
                        MoveDownDefaultComparer(lastNode, index);
                    }
                }
                else
                {
                    if (_comparer.Compare(lastNode.Priority, priority) < 0)
                    {
                        MoveUpCustomComparer(lastNode, index);
                    }
                    else
                    {
                        MoveDownCustomComparer(lastNode, index);
                    }
                }
            }

            HeapRemoveDone(Pal.Old(this.Store), newSize, index, Pal.Slice(Pal.Contents(_nodes), 0, _size));
            nodes[newSize] = default;
            _version++;
            return true;
        }

        /// <summary>
        ///  Removes all items from the <see cref="PriorityQueue{TElement, TPriority}"/>.
        /// </summary>
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        public void Clear()
        {
            if (RuntimeHelpers.IsReferenceOrContainsReferences<(TElement, TPriority)>())
            {
                // Clear the elements so that the gc can reclaim the references
                Array.Clear(_nodes, 0, _size);
            }
            _size = 0;
            _version++;
        }

        /// <summary>
        ///  Ensures that the <see cref="PriorityQueue{TElement, TPriority}"/> can hold up to
        ///  <paramref name="capacity"/> items without further expansion of its backing storage.
        /// </summary>
        /// <param name="capacity">The minimum capacity to be used.</param>
        /// <exception cref="ArgumentOutOfRangeException">
        ///  The specified <paramref name="capacity"/> is negative.
        /// </exception>
        /// <returns>The current capacity of the <see cref="PriorityQueue{TElement, TPriority}"/>.</returns>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("@this.SpecCapacity >= capacity")]
        [Ensures("Result == @this.SpecCapacity")]
        public int EnsureCapacity(int capacity)
        {
            ArgumentOutOfRangeException.ThrowIfNegative(capacity);

            if (_nodes.Length < capacity)
            {
                Grow(capacity);
                _version++;
            }

            return _nodes.Length;
        }

        /// <summary>
        ///  Sets the capacity to the actual number of items in the <see cref="PriorityQueue{TElement, TPriority}"/>,
        ///  if that is less than 90 percent of current capacity.
        /// </summary>
        /// <remarks>
        ///  This method can be used to minimize a collection's memory overhead
        ///  if no new elements will be added to the collection.
        /// </remarks>
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("@this.SpecCapacity <= Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity) || @this.SpecCapacity == @this.SpecCount")]
        public void TrimExcess()
        {
            int threshold = (int)(_nodes.Length * 0.9);
            if (_size < threshold)
            {
                Array.Resize(ref _nodes, _size);
                _version++;
            }
        }

        /// <summary>
        /// Grows the priority queue to match the specified min capacity.
        /// </summary>
        [Wrapping]
        [Requires("@this.SpecCapacity < minCapacity")]
        [Ensures("@this.Items == Pal.Old(@this.Items)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("@this.SpecCapacity >= minCapacity")]
        private void Grow(int minCapacity)
        {
            Debug.Assert(_nodes.Length < minCapacity);

            const int GrowFactor = 2;
            const int MinimumGrow = 4;

            int newcapacity = GrowFactor * _nodes.Length;

            // Allow the queue to grow to maximum possible capacity (~2G elements) before encountering overflow.
            // Note that this check works even when _nodes.Length overflowed thanks to the (uint) cast
            if ((uint)newcapacity > Array.MaxLength) newcapacity = Array.MaxLength;

            // Ensure minimum growth is respected.
            newcapacity = Math.Max(newcapacity, _nodes.Length + MinimumGrow);

            // If the computed capacity is still less than specified, set to the original argument.
            // Capacities exceeding Array.MaxLength will be surfaced as OutOfMemoryException by Array.Resize.
            if (newcapacity < minCapacity) newcapacity = minCapacity;

            Array.Resize(ref _nodes, newcapacity);
        }

        /// <summary>
        /// Removes the node from the root of the heap
        /// </summary>
        [Requires("Pal.IsHeap(@this.Items, @this.Order)")]
        [Requires("0 < @this.SpecCount && @this.SpecCount <= 536870912")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) - 1")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Permutation(Pal.Old(@this.Items), Pal.Snoc(@this.Items, Pal.Old(@this.Items)[0]))")]
        private void RemoveRootNode()
        {
            int lastNodeIndex = --_size;
            _version++;

            if (lastNodeIndex > 0)
            {
                (TElement Element, TPriority Priority) lastNode = _nodes[lastNodeIndex];
                HeapDownInit(Pal.Contents(_nodes), _size, lastNode, _comparer);
                if (_comparer == null)
                {
                    MoveDownDefaultComparer(lastNode, 0);
                }
                else
                {
                    MoveDownCustomComparer(lastNode, 0);
                }
            }

            HeapRemoveRoot(Pal.Old(this.Store), Pal.Old(this.SpecCount) - 1, Pal.Slice(Pal.Contents(_nodes), 0, _size));
            if (RuntimeHelpers.IsReferenceOrContainsReferences<(TElement, TPriority)>())
            {
                _nodes[lastNodeIndex] = default;
            }
        }

        // R26.10. The proof steps of a sift-up and a sift-down, each one of
        // Pulse.Lib.CSharp.Heap's lemmas. Ghost: the calls vanish from compiled code.

        [Lemma]
        [Requires("0 < n && n <= a.Length && Pal.IsHeap(Pal.Slice(a, 0, n - 1), c)")]
        [Ensures("Pal.HeapUp(a, n, n - 1, x, c, Pal.SetAt(Pal.Slice(a, 0, n), n - 1, x))")]
        [Ensures("Pal.Snoc(Pal.Slice(a, 0, n - 1), x) == Pal.SetAt(Pal.Slice(a, 0, n), n - 1, x)")]
        [PulseBody("Pulse.Lib.CSharp.Heap.up_init_at _ _ $(a) (I32.v $(n)) $(x) $(c)")]
        [Conditional("PAL")]
        private static void HeapUpInit(Seq<(TElement Element, TPriority Priority)> a, int n, (TElement Element, TPriority Priority) x, IComparer<TPriority>? c) { }

        [Lemma]
        [Requires("Pal.HeapUp(a, n, h, x, c, t) && h > 0 && !Pal.HeapUpStop(a, h, x, c)")]
        [Ensures("Pal.HeapUp(Pal.SetAt(a, h, a[(h - 1) / 4]), n, (h - 1) / 4, x, c, t)")]
        [PulseBody("Pulse.Lib.CSharp.Heap.up_step _ _ $(a) (I32.v $(n)) (I32.v $(h)) $(x) $(c) $(t)")]
        [Conditional("PAL")]
        private static void HeapUpStep(Seq<(TElement Element, TPriority Priority)> a, int n, int h, (TElement Element, TPriority Priority) x, IComparer<TPriority>? c, Seq<(TElement Element, TPriority Priority)> t) { }

        [Lemma]
        [Requires("Pal.HeapUp(a, n, h, x, c, t) && Pal.HeapUpStop(a, h, x, c)")]
        [Ensures("Pal.IsHeap(Pal.Slice(Pal.SetAt(a, h, x), 0, n), c)")]
        [Ensures("Pal.Permutation(t, Pal.Slice(Pal.SetAt(a, h, x), 0, n))")]
        [PulseBody("Pulse.Lib.CSharp.Heap.up_done _ _ $(a) (I32.v $(n)) (I32.v $(h)) $(x) $(c) $(t)")]
        [Conditional("PAL")]
        private static void HeapUpDone(Seq<(TElement Element, TPriority Priority)> a, int n, int h, (TElement Element, TPriority Priority) x, IComparer<TPriority>? c, Seq<(TElement Element, TPriority Priority)> t) { }

        [Lemma]
        [Requires("0 < n && n <= a.Length && Pal.IsHeap(Pal.Slice(a, 0, n), c)")]
        [Ensures("Pal.HeapDown(a, n, 0, x, c, Pal.SetAt(Pal.Slice(a, 0, n), 0, x))")]
        [PulseBody("Pulse.Lib.CSharp.Heap.down_init _ _ $(a) (I32.v $(n)) $(x) $(c)")]
        [Conditional("PAL")]
        private static void HeapDownInit(Seq<(TElement Element, TPriority Priority)> a, int n, (TElement Element, TPriority Priority) x, IComparer<TPriority>? c) { }

        [Lemma]
        [Requires("0 <= first && first < a.Length")]
        [Ensures("Pal.HeapMinChild(a, first, first + 1, first, c)")]
        [PulseBody("Pulse.Lib.CSharp.Heap.min_child_init _ _ $(a) (I32.v $(first)) $(c)")]
        [Conditional("PAL")]
        private static void HeapMinChildInit(Seq<(TElement Element, TPriority Priority)> a, int first, IComparer<TPriority>? c) { }

        [Lemma]
        [Requires("Pal.HeapMinChild(a, first, i, m, c) && i < a.Length")]
        [Ensures("Pal.Implies(Pal.Compare(c ?? Comparer<TPriority>.Default, a[i].Priority, a[m].Priority) < 0, Pal.HeapMinChild(a, first, i + 1, i, c))")]
        [Ensures("Pal.Implies(Pal.Compare(c ?? Comparer<TPriority>.Default, a[i].Priority, a[m].Priority) >= 0, Pal.HeapMinChild(a, first, i + 1, m, c))")]
        [PulseBody("Pulse.Lib.CSharp.Heap.min_child_step _ _ $(a) $(first) (I32.v $(i)) (I32.v $(m)) $(c)")]
        [Conditional("PAL")]
        private static void HeapMinChildStep(Seq<(TElement Element, TPriority Priority)> a, SpecInt first, int i, int m, IComparer<TPriority>? c) { }

        [Lemma]
        [Requires("Pal.HeapDown(a, n, h, x, c, t) && 4 * h + 1 < n && Pal.HeapMinChild(a, 4 * h + 1, (4 * h + 5 < n ? 4 * h + 5 : n), m, c) && !Pal.HeapDownStop(a, n, h, x, m, c)")]
        [Ensures("Pal.HeapDown(Pal.SetAt(a, h, a[m]), n, m, x, c, t)")]
        [PulseBody("Pulse.Lib.CSharp.Heap.down_step _ _ $(a) (I32.v $(n)) (I32.v $(h)) $(x) (I32.v $(m)) $(c) $(t)")]
        [Conditional("PAL")]
        private static void HeapDownStep(Seq<(TElement Element, TPriority Priority)> a, int n, int h, (TElement Element, TPriority Priority) x, int m, IComparer<TPriority>? c, Seq<(TElement Element, TPriority Priority)> t) { }

        [Lemma]
        [Requires("Pal.HeapDown(a, n, h, x, c, t) && Pal.HeapDownStop(a, n, h, x, m, c)")]
        [Ensures("Pal.IsHeap(Pal.Slice(Pal.SetAt(a, h, x), 0, n), c)")]
        [Ensures("Pal.Permutation(t, Pal.Slice(Pal.SetAt(a, h, x), 0, n))")]
        [PulseBody("Pulse.Lib.CSharp.Heap.down_done _ _ $(a) (I32.v $(n)) (I32.v $(h)) $(x) (I32.v $(m)) $(c) $(t)")]
        [Conditional("PAL")]
        private static void HeapDownDone(Seq<(TElement Element, TPriority Priority)> a, int n, int h, (TElement Element, TPriority Priority) x, int m, IComparer<TPriority>? c, Seq<(TElement Element, TPriority Priority)> t) { }

        [Lemma]
        [Requires("0 < n && n <= a.Length && Pal.IsHeap(Pal.Slice(a, 0, n), c)")]
        [Requires("Pal.Compare(c ?? Comparer<TPriority>.Default, x.Priority, a[0].Priority) <= 0")]
        [Ensures("Pal.IsHeap(Pal.Slice(Pal.SetAt(a, 0, x), 0, n), c)")]
        [Ensures("Pal.Permutation(Pal.SetAt(Pal.Slice(a, 0, n), 0, x), Pal.Slice(Pal.SetAt(a, 0, x), 0, n))")]
        [PulseBody("Pulse.Lib.CSharp.Heap.replace_root _ _ $(a) (I32.v $(n)) $(x) $(c)")]
        [Conditional("PAL")]
        private static void HeapReplaceRoot(Seq<(TElement Element, TPriority Priority)> a, int n, (TElement Element, TPriority Priority) x, IComparer<TPriority>? c) { }

        [Lemma]
        [Requires("Pal.HeapDown(a, n, h, x, c, t)")]
        [Requires("(i == 4 * h + 1 && i >= n) || (Pal.IsHeap(Pal.Slice(Pal.SetAt(a, h, x), 0, n), c) && Pal.Permutation(t, Pal.Slice(Pal.SetAt(a, h, x), 0, n)))")]
        [Ensures("Pal.IsHeap(Pal.Slice(Pal.SetAt(a, h, x), 0, n), c)")]
        [Ensures("Pal.Permutation(t, Pal.Slice(Pal.SetAt(a, h, x), 0, n))")]
        [PulseBody("Pulse.Lib.CSharp.Heap.down_finish _ _ $(a) (I32.v $(n)) (I32.v $(h)) $(x) $(c) $(t) (I32.v $(i))")]
        [Conditional("PAL")]
        private static void HeapDownFinish(Seq<(TElement Element, TPriority Priority)> a, int n, int h, (TElement Element, TPriority Priority) x, IComparer<TPriority>? c, Seq<(TElement Element, TPriority Priority)> t, int i) { }

        [Lemma]
        [Requires("0 <= n && n < s.Length && Pal.Implies(n == 0, r.Length == 0) && Pal.Implies(n > 0, Pal.Permutation(Pal.SetAt(Pal.Slice(s, 0, n), 0, s[n]), r))")]
        [Ensures("Pal.Permutation(Pal.Slice(s, 0, n + 1), Pal.Snoc(r, s[0]))")]
        [PulseBody("Pulse.Lib.CSharp.Heap.remove_root _ _ $(s) $(n) $(r)")]
        [Conditional("PAL")]
        private static void HeapRemoveRoot(Seq<(TElement Element, TPriority Priority)> s, SpecInt n, Seq<(TElement Element, TPriority Priority)> r) { }

        // Remove's proof steps (pal-csharp doc/translation.md §33). The last node, put in the
        // removed node's hole, meets MoveUp*'s or MoveDown*'s precondition; and the old heap
        // is the new one with the removed node put back.
        [Lemma]
        [Requires("0 <= i && i < n && n < s.Length && Pal.IsHeap(Pal.Slice(s, 0, n + 1), c)")]
        [Ensures("Pal.Implies(Pal.Compare(c ?? Comparer<TPriority>.Default, s[n].Priority, s[i].Priority) < 0, Pal.HeapUp(s, n, i, s[n], c, Pal.SetAt(Pal.Slice(s, 0, n), i, s[n])))")]
        [Ensures("Pal.Implies(Pal.Compare(c ?? Comparer<TPriority>.Default, s[n].Priority, s[i].Priority) >= 0, Pal.HeapDown(s, n, i, s[n], c, Pal.SetAt(Pal.Slice(s, 0, n), i, s[n])))")]
        [PulseBody("PriorityQueueRemove.remove_init _ _ $(s) (I32.v $(n)) (I32.v $(i)) $(c)")]
        [Conditional("PAL")]
        private static void HeapRemoveInit(Seq<(TElement Element, TPriority Priority)> s, int n, int i, IComparer<TPriority>? c) { }

        [Lemma]
        [Requires("0 <= i && i <= n && n < s.Length")]
        [Requires("Pal.Implies(i < n, Pal.Permutation(Pal.SetAt(Pal.Slice(s, 0, n), i, s[n]), r))")]
        [Requires("Pal.Implies(i == n, r == Pal.Slice(s, 0, n))")]
        [Ensures("Pal.Permutation(Pal.Slice(s, 0, n + 1), Pal.Snoc(r, s[i]))")]
        [PulseBody("PriorityQueueRemove.remove_done _ _ $(s) (I32.v $(n)) (I32.v $(i)) $(r)")]
        [Conditional("PAL")]
        private static void HeapRemoveDone(Seq<(TElement Element, TPriority Priority)> s, int n, int i, Seq<(TElement Element, TPriority Priority)> r) { }

        /// <summary>
        /// Gets the index of an element's parent.
        /// </summary>
        [Requires("index > 0")]
        [Ensures("Result == (index - 1) / 4")]
        private static int GetParentIndex(int index) => (index - 1) >> Log2Arity;

        /// <summary>
        /// Gets the index of the first child of an element.
        /// </summary>
        [Requires("0 <= index && index <= 536870911")]
        [Ensures("Result == 4 * index + 1")]
        private static int GetFirstChildIndex(int index) => (index << Log2Arity) + 1;

        /// <summary>
        /// Converts an unordered list into a heap.
        /// </summary>
        private void Heapify()
        {
            // Leaves of the tree are in fact 1-element heaps, for which there
            // is no need to correct them. The heap property needs to be restored
            // only for higher nodes, starting from the first node that has children.
            // It is the parent of the very last element in the array.

            (TElement Element, TPriority Priority)[] nodes = _nodes;
            int lastParentWithChildren = GetParentIndex(_size - 1);

            if (_comparer == null)
            {
                for (int index = lastParentWithChildren; index >= 0; --index)
                {
                    MoveDownDefaultComparer(nodes[index], index);
                }
            }
            else
            {
                for (int index = lastParentWithChildren; index >= 0; --index)
                {
                    MoveDownCustomComparer(nodes[index], index);
                }
            }
        }

        /// <summary>
        /// Moves a node up in the tree to restore heap order.
        /// </summary>
        [Requires("@this.Order == null")]
        [Requires("0 <= nodeIndex && nodeIndex < @this.SpecCount")]
        [Requires("Pal.HeapUp(@this.Store, @this.SpecCount, nodeIndex, node, @this.Order, Pal.SetAt(@this.Items, nodeIndex, node))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Permutation(Pal.Old(Pal.SetAt(@this.Items, nodeIndex, node)), @this.Items)")]
        private void MoveUpDefaultComparer((TElement Element, TPriority Priority) node, int nodeIndex)
        {
            // Instead of swapping items all the way to the root, we will perform
            // a similar optimization as in the insertion sort.

            Debug.Assert(_comparer is null);
            Debug.Assert(0 <= nodeIndex && nodeIndex < _size);

            (TElement Element, TPriority Priority)[] nodes = _nodes;

            while (nodeIndex > 0)
            {
                Pal.Invariant(Pal.HeapUp(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer,
                    Pal.Old(Pal.SetAt(this.Items, nodeIndex, node))));
                Pal.Invariant(Pal.Implies(Pal.Broke(), Pal.HeapUpStop(Pal.Contents(_nodes), nodeIndex, node, _comparer)));
                Pal.Decreases(nodeIndex);
                int parentIndex = GetParentIndex(nodeIndex);
                (TElement Element, TPriority Priority) parent = nodes[parentIndex];

                if (Comparer<TPriority>.Default.Compare(node.Priority, parent.Priority) < 0)
                {
                    HeapUpStep(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)));
                    nodes[nodeIndex] = parent;
                    nodeIndex = parentIndex;
                }
                else
                {
                    break;
                }
            }

            HeapUpDone(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)));
            nodes[nodeIndex] = node;
        }

        /// <summary>
        /// Moves a node up in the tree to restore heap order.
        /// </summary>
        [Requires("@this.Order != null")]
        [Requires("0 <= nodeIndex && nodeIndex < @this.SpecCount")]
        [Requires("Pal.HeapUp(@this.Store, @this.SpecCount, nodeIndex, node, @this.Order, Pal.SetAt(@this.Items, nodeIndex, node))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Permutation(Pal.Old(Pal.SetAt(@this.Items, nodeIndex, node)), @this.Items)")]
        private void MoveUpCustomComparer((TElement Element, TPriority Priority) node, int nodeIndex)
        {
            // Instead of swapping items all the way to the root, we will perform
            // a similar optimization as in the insertion sort.

            Debug.Assert(_comparer is not null);
            Debug.Assert(0 <= nodeIndex && nodeIndex < _size);

            IComparer<TPriority> comparer = _comparer;
            (TElement Element, TPriority Priority)[] nodes = _nodes;

            while (nodeIndex > 0)
            {
                Pal.Invariant(Pal.HeapUp(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer,
                    Pal.Old(Pal.SetAt(this.Items, nodeIndex, node))));
                Pal.Invariant(Pal.Implies(Pal.Broke(), Pal.HeapUpStop(Pal.Contents(_nodes), nodeIndex, node, _comparer)));
                Pal.Decreases(nodeIndex);
                int parentIndex = GetParentIndex(nodeIndex);
                (TElement Element, TPriority Priority) parent = nodes[parentIndex];

                if (comparer.Compare(node.Priority, parent.Priority) < 0)
                {
                    HeapUpStep(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)));
                    nodes[nodeIndex] = parent;
                    nodeIndex = parentIndex;
                }
                else
                {
                    break;
                }
            }

            HeapUpDone(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)));
            nodes[nodeIndex] = node;
        }

        /// <summary>
        /// Moves a node down in the tree to restore heap order.
        /// </summary>
        [Requires("@this.Order == null")]
        [Requires("0 <= nodeIndex && nodeIndex < @this.SpecCount")]
        // (nodeIndex << 2) + 1 wraps for nodeIndex >= 2^29; see the spec findings.
        [Requires("@this.SpecCount <= 536870912")]
        [Requires("Pal.HeapDown(@this.Store, @this.SpecCount, nodeIndex, node, @this.Order, Pal.SetAt(@this.Items, nodeIndex, node))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Permutation(Pal.Old(Pal.SetAt(@this.Items, nodeIndex, node)), @this.Items)")]
        private void MoveDownDefaultComparer((TElement Element, TPriority Priority) node, int nodeIndex)
        {
            // The node to move down will not actually be swapped every time.
            // Rather, values on the affected path will be moved up, thus leaving a free spot
            // for this value to drop in. Similar optimization as in the insertion sort.

            Debug.Assert(_comparer is null);
            Debug.Assert(0 <= nodeIndex && nodeIndex < _size);

            (TElement Element, TPriority Priority)[] nodes = _nodes;
            int size = _size;

            int i;
            while ((i = GetFirstChildIndex(nodeIndex)) < size)
            {
                Pal.Invariant(Pal.Implies(!Pal.Broke(), i == 4 * nodeIndex + 1));
                Pal.Invariant(Pal.HeapDown(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node))));
                Pal.Invariant(Pal.Implies(Pal.Broke(), Pal.IsHeap(Pal.Slice(Pal.SetAt(Pal.Contents(_nodes), nodeIndex, node), 0, _size), _comparer) && Pal.Permutation(Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)), Pal.Slice(Pal.SetAt(Pal.Contents(_nodes), nodeIndex, node), 0, _size))));
                Pal.Decreases(_size - nodeIndex);
                // Find the child node with the minimal priority
                (TElement Element, TPriority Priority) minChild = nodes[i];
                int minChildIndex = i;
                HeapMinChildInit(Pal.Contents(_nodes), i, _comparer);

                int childIndexUpperBound = Math.Min(i + Arity, size);
                while (++i < childIndexUpperBound)
                {
                    Pal.Invariant(4 * nodeIndex + 1 < i && i <= childIndexUpperBound && childIndexUpperBound <= _size);
                    Pal.Invariant(Pal.HeapMinChild(Pal.Contents(_nodes), 4 * nodeIndex + 1, i, minChildIndex, _comparer));
                    Pal.Invariant(Pal.Same(minChild, Pal.Contents(_nodes)[minChildIndex]));
                    Pal.Decreases(childIndexUpperBound - i);
                    HeapMinChildStep(Pal.Contents(_nodes), 4 * nodeIndex + 1, i, minChildIndex, _comparer);
                    (TElement Element, TPriority Priority) nextChild = nodes[i];
                    if (Comparer<TPriority>.Default.Compare(nextChild.Priority, minChild.Priority) < 0)
                    {
                        minChild = nextChild;
                        minChildIndex = i;
                    }
                }

                // Heap property is satisfied; insert node in this location.
                if (Comparer<TPriority>.Default.Compare(node.Priority, minChild.Priority) <= 0)
                {
                    HeapDownDone(Pal.Contents(_nodes), _size, nodeIndex, node, minChildIndex, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)));
                    break;
                }

                HeapDownStep(Pal.Contents(_nodes), _size, nodeIndex, node, minChildIndex, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)));
                // Move the minimal child up by one node and
                // continue recursively from its location.
                nodes[nodeIndex] = minChild;
                nodeIndex = minChildIndex;
            }

            HeapDownFinish(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)), i);
            nodes[nodeIndex] = node;
        }

        /// <summary>
        /// Moves a node down in the tree to restore heap order.
        /// </summary>
        [Requires("@this.Order != null")]
        [Requires("0 <= nodeIndex && nodeIndex < @this.SpecCount")]
        // (nodeIndex << 2) + 1 wraps for nodeIndex >= 2^29; see the spec findings.
        [Requires("@this.SpecCount <= 536870912")]
        [Requires("Pal.HeapDown(@this.Store, @this.SpecCount, nodeIndex, node, @this.Order, Pal.SetAt(@this.Items, nodeIndex, node))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.Order == Pal.Old(@this.Order)")]
        [Ensures("Pal.IsHeap(@this.Items, @this.Order)")]
        [Ensures("Pal.Permutation(Pal.Old(Pal.SetAt(@this.Items, nodeIndex, node)), @this.Items)")]
        private void MoveDownCustomComparer((TElement Element, TPriority Priority) node, int nodeIndex)
        {
            // The node to move down will not actually be swapped every time.
            // Rather, values on the affected path will be moved up, thus leaving a free spot
            // for this value to drop in. Similar optimization as in the insertion sort.

            Debug.Assert(_comparer is not null);
            Debug.Assert(0 <= nodeIndex && nodeIndex < _size);

            IComparer<TPriority> comparer = _comparer;
            (TElement Element, TPriority Priority)[] nodes = _nodes;
            int size = _size;

            int i;
            while ((i = GetFirstChildIndex(nodeIndex)) < size)
            {
                Pal.Invariant(Pal.Implies(!Pal.Broke(), i == 4 * nodeIndex + 1));
                Pal.Invariant(Pal.HeapDown(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node))));
                Pal.Invariant(Pal.Implies(Pal.Broke(), Pal.IsHeap(Pal.Slice(Pal.SetAt(Pal.Contents(_nodes), nodeIndex, node), 0, _size), _comparer) && Pal.Permutation(Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)), Pal.Slice(Pal.SetAt(Pal.Contents(_nodes), nodeIndex, node), 0, _size))));
                Pal.Decreases(_size - nodeIndex);
                // Find the child node with the minimal priority
                (TElement Element, TPriority Priority) minChild = nodes[i];
                int minChildIndex = i;
                HeapMinChildInit(Pal.Contents(_nodes), i, _comparer);

                int childIndexUpperBound = Math.Min(i + Arity, size);
                while (++i < childIndexUpperBound)
                {
                    Pal.Invariant(4 * nodeIndex + 1 < i && i <= childIndexUpperBound && childIndexUpperBound <= _size);
                    Pal.Invariant(Pal.HeapMinChild(Pal.Contents(_nodes), 4 * nodeIndex + 1, i, minChildIndex, _comparer));
                    Pal.Invariant(Pal.Same(minChild, Pal.Contents(_nodes)[minChildIndex]));
                    Pal.Decreases(childIndexUpperBound - i);
                    HeapMinChildStep(Pal.Contents(_nodes), 4 * nodeIndex + 1, i, minChildIndex, _comparer);
                    (TElement Element, TPriority Priority) nextChild = nodes[i];
                    if (comparer.Compare(nextChild.Priority, minChild.Priority) < 0)
                    {
                        minChild = nextChild;
                        minChildIndex = i;
                    }
                }

                // Heap property is satisfied; insert node in this location.
                if (comparer.Compare(node.Priority, minChild.Priority) <= 0)
                {
                    HeapDownDone(Pal.Contents(_nodes), _size, nodeIndex, node, minChildIndex, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)));
                    break;
                }

                HeapDownStep(Pal.Contents(_nodes), _size, nodeIndex, node, minChildIndex, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)));
                // Move the minimal child up by one node and continue recursively from its location.
                nodes[nodeIndex] = minChild;
                nodeIndex = minChildIndex;
            }

            HeapDownFinish(Pal.Contents(_nodes), _size, nodeIndex, node, _comparer, Pal.Old(Pal.SetAt(this.Items, nodeIndex, node)), i);
            nodes[nodeIndex] = node;
        }

        /// <summary>
        /// Scans the heap for the first index containing an element equal to the specified parameter.
        /// </summary>
        [Ensures("-1 <= Result && Result < @this.SpecCount")]
        [Ensures("Pal.Implies(Result >= 0, Result < @this.Items.Length && PriorityQueue<TElement, TPriority>.ElemEq(equalityComparer, element, @this.Items[Result].Element))")]
        [Ensures("PriorityQueue<TElement, TPriority>.NoMatch(equalityComparer, element, @this.Items, Result >= 0 ? Result : @this.SpecCount)")]
        private int FindIndex(TElement element, IEqualityComparer<TElement>? equalityComparer)
        {
            equalityComparer ??= EqualityComparer<TElement>.Default;
            ReadOnlySpan<(TElement Element, TPriority Priority)> nodes = _nodes.AsSpan(0, _size);

            // Currently the JIT doesn't optimize direct EqualityComparer<T>.Default.Equals
            // calls for reference types, so we want to cache the comparer instance instead.
            // TODO https://github.com/dotnet/runtime/issues/10050: Update if this changes in the future.
            if (typeof(TElement).IsValueType && equalityComparer == EqualityComparer<TElement>.Default)
            {
                for (int i = 0; i < nodes.Length; i++)
                {
                    Pal.Invariant(0 <= i && i <= nodes.Length);
                    Pal.Invariant(NoMatch(equalityComparer, element, Pal.Contents(nodes), i));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), i < nodes.Length && Pal.ReturnValue<int>() == i &&
                        ElemEq(equalityComparer, element, Pal.Contents(nodes)[i].Element)));
                    if (EqualityComparer<TElement>.Default.Equals(element, nodes[i].Element))
                    {
                        return i;
                    }
                }
            }
            else
            {
                for (int i = 0; i < nodes.Length; i++)
                {
                    Pal.Invariant(0 <= i && i <= nodes.Length);
                    Pal.Invariant(NoMatch(equalityComparer, element, Pal.Contents(nodes), i));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), i < nodes.Length && Pal.ReturnValue<int>() == i &&
                        ElemEq(equalityComparer, element, Pal.Contents(nodes)[i].Element)));
                    if (equalityComparer.Equals(element, nodes[i].Element))
                    {
                        return i;
                    }
                }
            }

            return -1;
        }

        /// <summary><paramref name="c"/>, or the default comparer when it is null, deems <paramref name="x"/> equal to <paramref name="y"/>.</summary>
        [Spec]
        [PulseBody("PriorityQueueRemove.elem_eq $(c) $(x) $(y)")]
        public static bool ElemEq(IEqualityComparer<TElement>? c, TElement x, TElement y) => throw new InvalidOperationException();

        /// <summary>No node of <paramref name="s"/> below <paramref name="i"/> holds an element equal to <paramref name="x"/>.</summary>
        [Spec]
        [PulseBody("PriorityQueueRemove.no_match $(c) $(x) $(s) $(i)")]
        public static bool NoMatch(IEqualityComparer<TElement>? c, TElement x, Seq<(TElement Element, TPriority Priority)> s, SpecInt i) => throw new InvalidOperationException();

        /// <summary>
        /// Initializes the custom comparer to be used internally by the heap.
        /// </summary>
        [Ensures("(Result ?? Comparer<TPriority>.Default) == (comparer ?? Comparer<TPriority>.Default)")]
        private static IComparer<TPriority>? InitializeComparer(IComparer<TPriority>? comparer)
        {
            if (typeof(TPriority).IsValueType)
            {
                if (comparer == Comparer<TPriority>.Default)
                {
                    // if the user manually specifies the default comparer,
                    // revert to using the optimized path.
                    return null;
                }

                return comparer;
            }
            else
            {
                // Currently the JIT doesn't optimize direct Comparer<T>.Default.Compare
                // calls for reference types, so we want to cache the comparer instance instead.
                // TODO https://github.com/dotnet/runtime/issues/10050: Update if this changes in the future.
                return comparer ?? Comparer<TPriority>.Default;
            }
        }

        /// <summary>
        ///  Enumerates the contents of a <see cref="PriorityQueue{TElement, TPriority}"/>, without any ordering guarantees.
        /// </summary>
        [DebuggerDisplay("Count = {Count}")]
        [DebuggerTypeProxy(typeof(PriorityQueueDebugView<,>))]
        public sealed class UnorderedItemsCollection : IReadOnlyCollection<(TElement Element, TPriority Priority)>, ICollection
        {
            internal readonly PriorityQueue<TElement, TPriority> _queue;

            [Ensures("ReferenceEquals(@this._queue, queue)")]
            internal UnorderedItemsCollection(PriorityQueue<TElement, TPriority> queue) => _queue = queue;

            [Ensures("Result == @this._queue.SpecCount")]
            public int Count => _queue._size;
            object ICollection.SyncRoot => this;
            bool ICollection.IsSynchronized => false;

            void ICollection.CopyTo(Array array, int index)
            {
                ArgumentNullException.ThrowIfNull(array);

                if (array.Rank != 1)
                {
                    throw new ArgumentException(SR.Arg_RankMultiDimNotSupported, nameof(array));
                }

                if (array.GetLowerBound(0) != 0)
                {
                    throw new ArgumentException(SR.Arg_NonZeroLowerBound, nameof(array));
                }

                if (index < 0 || index > array.Length)
                {
                    throw new ArgumentOutOfRangeException(nameof(index), index, SR.ArgumentOutOfRange_IndexMustBeLessOrEqual);
                }

                if (array.Length - index < _queue._size)
                {
                    throw new ArgumentException(SR.Argument_InvalidOffLen);
                }

                try
                {
                    Array.Copy(_queue._nodes, 0, array, index, _queue._size);
                }
                catch (ArrayTypeMismatchException)
                {
                    throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                }
            }

            /// <summary>
            ///  Enumerates the element and priority pairs of a <see cref="PriorityQueue{TElement, TPriority}"/>,
            ///  without any ordering guarantees.
            /// </summary>
            public struct Enumerator : IEnumerator<(TElement Element, TPriority Priority)>
            {
                private readonly PriorityQueue<TElement, TPriority> _queue;
                private readonly int _version;
                private int _index;
                private (TElement, TPriority) _current;

                [Ensures("ReferenceEquals(@this._queue, queue) && @this._version == queue.SpecVersion && @this._index == 0")]
                internal Enumerator(PriorityQueue<TElement, TPriority> queue)
                {
                    _queue = queue;
                    _index = 0;
                    _version = queue._version;
                    _current = default;
                }

                /// <summary>
                /// Releases all resources used by the <see cref="Enumerator"/>.
                /// </summary>
                [Ensures("true")]
                public void Dispose() { }

                /// <summary>
                /// Advances the enumerator to the next element of the <see cref="UnorderedItems"/>.
                /// </summary>
                /// <returns><see langword="true"/> if the enumerator was successfully advanced to the next element; <see langword="false"/> if the enumerator has passed the end of the collection.</returns>
                [Requires("-1 <= @this._index && @this._index <= @this._queue.SpecCount")]
                [Throws(typeof(InvalidOperationException), "@this._version != @this._queue.SpecVersion")]
                [Ensures("@this._version == @this._queue.SpecVersion")]
                [Ensures("-1 <= @this._index && @this._index <= @this._queue.SpecCount")]
                [Ensures("Result == (0 <= Pal.Old(@this._index) && Pal.Old(@this._index) < @this._queue.SpecCount)")]
                [Ensures("Pal.Implies(Result, @this._index == Pal.Old(@this._index) + 1 && Pal.Same(@this._current, @this._queue.Items[Pal.Old(@this._index)]))")]
                [Ensures("Pal.Implies(!Result, @this._index == -1)")]
                public bool MoveNext()
                {
                    PriorityQueue<TElement, TPriority> localQueue = _queue;

                    if (_version != localQueue._version)
                    {
                        ThrowHelper.ThrowVersionCheckFailed();
                    }

                    if ((uint)_index < (uint)localQueue._size)
                    {
                        _current = localQueue._nodes[_index];
                        _index++;
                        return true;
                    }

                    _current = default;
                    _index = -1;
                    return false;
                }

                /// <summary>
                /// Gets the element at the current position of the enumerator.
                /// </summary>
                [Ensures("Pal.Same(Result, @this._current)")]
                public (TElement Element, TPriority Priority) Current => _current;
                [Ensures("Pal.Boxes(Result, @this._current)")]
                object IEnumerator.Current => _current;

                [Throws(typeof(InvalidOperationException), "@this._version != @this._queue.SpecVersion")]
                [Ensures("@this._version == @this._queue.SpecVersion && @this._index == 0")]
                void IEnumerator.Reset()
                {
                    if (_version != _queue._version)
                    {
                        ThrowHelper.ThrowVersionCheckFailed();
                    }

                    _index = 0;
                    _current = default;
                }
            }

            /// <summary>
            /// Returns an enumerator that iterates through the <see cref="UnorderedItems"/>.
            /// </summary>
            /// <returns>An <see cref="Enumerator"/> for the <see cref="UnorderedItems"/>.</returns>
            [Ensures("ReferenceEquals(Result._queue, @this._queue) && Result._version == @this._queue.SpecVersion && Result._index == 0")]
            public Enumerator GetEnumerator() => new Enumerator(_queue);

            [Ensures("Pal.Implies(@this._queue.SpecCount != 0, Pal.Exists((PriorityQueue<TElement, TPriority>.UnorderedItemsCollection.Enumerator e) => Pal.Boxes(Result, e) && " +
                "ReferenceEquals(e._queue, @this._queue) && e._version == @this._queue.SpecVersion && e._index == 0))")]
            IEnumerator<(TElement Element, TPriority Priority)> IEnumerable<(TElement Element, TPriority Priority)>.GetEnumerator() =>
                _queue.Count == 0 ? EnumerableHelpers.GetEmptyEnumerator<(TElement Element, TPriority Priority)>() :
                GetEnumerator();

            [Ensures("Pal.Implies(@this._queue.SpecCount != 0, Pal.Exists((PriorityQueue<TElement, TPriority>.UnorderedItemsCollection.Enumerator e) => Pal.Boxes(Result, e) && " +
                "ReferenceEquals(e._queue, @this._queue) && e._version == @this._queue.SpecVersion && e._index == 0))")]
            IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<(TElement Element, TPriority Priority)>)this).GetEnumerator();
        }
    }
}
