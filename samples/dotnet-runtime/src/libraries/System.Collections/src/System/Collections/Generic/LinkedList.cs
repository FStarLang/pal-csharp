// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.ComponentModel;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.Serialization;
using PalLang;

namespace System.Collections.Generic
{
    /// <summary>The abstract state of a <see cref="LinkedList{T}"/>.</summary>
    [Spec]
    public struct LinkedListModel<T>
    {
        public Seq<LinkedListNode<T>> Nodes;
        public Seq<T> Items;
        public SpecInt Count;
        public SpecInt Version;
    }

    [DebuggerTypeProxy(typeof(ICollectionDebugView<>))]
    [DebuggerDisplay("Count = {Count}")]
    [Serializable]
    [System.Runtime.CompilerServices.TypeForwardedFrom("System, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    [Invariant("SpecRing.Ring<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, @this)")]
    public class LinkedList<T> : ICollection<T>, ICollection, IReadOnlyCollection<T>, ISerializable, IDeserializationCallback
    {
        // This LinkedList is a doubly-Linked circular list.
        internal LinkedListNode<T>? head;
        internal int count;
        [Wrapping] internal int version;
        private SerializationInfo? _siInfo; //A temporary variable which we need during deserialization.

        // names for serialization
        private const string VersionName = "Version"; // Do not rename (binary serialization)
        private const string CountName = "Count"; // Do not rename (binary serialization)
        private const string ValuesName = "Data"; // Do not rename (binary serialization)

        [Ensures("@this.SpecCount == 0 && @this.SpecNodes.Length == 0 && @this.SpecItems.Length == 0")]
        public LinkedList()
        {
        }

        [Requires("Pal.Contents(collection).Length < int.MaxValue")]
        [Ensures("@this.SpecCount == Pal.Contents(collection).Length && @this.SpecItems == Pal.Contents(collection)")]
        public LinkedList(IEnumerable<T> collection)
        {
            ArgumentNullException.ThrowIfNull(collection);

            foreach (T item in collection)
            {
                Pal.Invariant(this.SpecCount == Pal.Index(item) && this.SpecItems == Pal.Slice(Pal.Contents(collection), 0, Pal.Index(item)));
                AddLast(item);
            }
        }

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        [EditorBrowsable(EditorBrowsableState.Never)]
        protected LinkedList(SerializationInfo info, StreamingContext context)
        {
            _siInfo = info;
        }

        [Refine("Result.Count >= 0 && Result.Nodes.Length == Result.Count && Result.Items.Length == Result.Count")]
        [Model]
        private LinkedListModel<T> Model => new LinkedListModel<T>
        {
            Nodes = SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count),
            Items = SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)),
            Count = count,
            Version = version,
        };

        /// <summary>The nodes, from the first.</summary>
        [Spec]
        public Seq<LinkedListNode<T>> SpecNodes => Model.Nodes;

        /// <summary>The items, from the first node's.</summary>
        [Spec]
        public Seq<T> SpecItems => Model.Items;

        [Spec]
        public SpecInt SpecCount => Model.Count;

        [Spec]
        public SpecInt SpecVersion => Model.Version;

        /// <summary>A version after one mutation: <c>version++</c> on a wrapping counter.</summary>
        [Spec]
        [PulseBody("(if $(v) = 2147483647 then -2147483648 else $(v) + 1)")]
        public static SpecInt Bumped(SpecInt v) => throw new InvalidOperationException();

        [Ensures("Result == @this.SpecCount")]
        public int Count
        {
            get { return count; }
        }

        [Ensures("@this.SpecCount == 0 ? Result == null : Result == @this.SpecNodes[0]")]
        public LinkedListNode<T>? First
        {
            get
            {
                SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
                return head;
            }
        }

        [Ensures("@this.SpecCount == 0 ? Result == null : Result == @this.SpecNodes[@this.SpecCount - 1]")]
        public LinkedListNode<T>? Last
        {
            get
            {
                SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
                return head?.prev;
            }
        }

        bool ICollection<T>.IsReadOnly
        {
            get { return false; }
        }

        [Requires("@this.SpecCount < int.MaxValue")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), Pal.Old(@this.SpecCount), value)")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        void ICollection<T>.Add(T value)
        {
            AddLast(value);
        }

        [Requires("Pal.InRegion(node) && @this.SpecCount < int.MaxValue")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Pos<LinkedListNode<T>>(@this.SpecNodes, node) < 0")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecNodes == SpecRing.InsertAt(Pal.Old(@this.SpecNodes), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node) + 1, Result)")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node) + 1, value)")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public LinkedListNode<T> AddAfter(LinkedListNode<T> node, T value)
        {
            ValidateNode(node);
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, node, this);
            SpecRing.Neighbours<LinkedListNode<T>>(h0.Value, head, count, node);
            SpecRing.Ends<LinkedListNode<T>>(h0.Value, head, count);
            LinkedListNode<T> result = new LinkedListNode<T>(node.list!, value);
            Ghost<SpecHeap<LinkedListNode<T>>> ha = Pal.Heap<LinkedListNode<T>>();
            SpecRing.Allocated<LinkedListNode<T>>(h0.Value, ha.Value, head, count, result);
            InternalInsertNodeBefore(node.next!, result);
            SpecRing.Adopted<LinkedListNode<T>, LinkedList<T>>(h0.Value, ha.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, head, result, SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(h0.Value, hd0.Value, n0.Value), node) + 1, this);
            return result;
        }

        [Requires("Pal.InRegion(newNode) && Pal.InRegion(node) && @this.SpecCount < int.MaxValue")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Pos<LinkedListNode<T>>(@this.SpecNodes, node) < 0 || SpecRing.Owner<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), newNode) != null")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecNodes == SpecRing.InsertAt(Pal.Old(@this.SpecNodes), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node) + 1, newNode)")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node) + 1, Pal.Old(SpecRing.Item<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), newNode)))")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public void AddAfter(LinkedListNode<T> node, LinkedListNode<T> newNode)
        {
            ValidateNode(node);
            ValidateNewNode(newNode);
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, node, this);
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, newNode, this);
            SpecRing.Neighbours<LinkedListNode<T>>(h0.Value, head, count, node);
            SpecRing.Ends<LinkedListNode<T>>(h0.Value, head, count);
            InternalInsertNodeBefore(node.next!, newNode);
            Ghost<SpecHeap<LinkedListNode<T>>> h1 = Pal.Heap<LinkedListNode<T>>();
            newNode.list = this;
            SpecRing.Reowned<LinkedListNode<T>>(h1.Value, Pal.Heap<LinkedListNode<T>>(), head, count, newNode);
            SpecRing.Reattached<LinkedListNode<T>, LinkedList<T>>(h0.Value, h1.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, head, newNode, SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(h0.Value, hd0.Value, n0.Value), node) + 1, this);
        }

        [Requires("Pal.InRegion(node) && @this.SpecCount < int.MaxValue")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Pos<LinkedListNode<T>>(@this.SpecNodes, node) < 0")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecNodes == SpecRing.InsertAt(Pal.Old(@this.SpecNodes), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node), Result)")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node), value)")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public LinkedListNode<T> AddBefore(LinkedListNode<T> node, T value)
        {
            ValidateNode(node);
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, node, this);
            SpecRing.Neighbours<LinkedListNode<T>>(h0.Value, head, count, node);
            SpecRing.Ends<LinkedListNode<T>>(h0.Value, head, count);
            LinkedListNode<T> result = new LinkedListNode<T>(node.list!, value);
            Ghost<SpecHeap<LinkedListNode<T>>> ha = Pal.Heap<LinkedListNode<T>>();
            SpecRing.Allocated<LinkedListNode<T>>(h0.Value, ha.Value, head, count, result);
            InternalInsertNodeBefore(node, result);
            if (node == head)
            {
                SpecRing.Rotated<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, n0.Value, SpecRing.Nodes<LinkedListNode<T>>(h0.Value, hd0.Value, n0.Value), result);
                head = result;
            }
            SpecRing.Adopted<LinkedListNode<T>, LinkedList<T>>(h0.Value, ha.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, head, result, SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(h0.Value, hd0.Value, n0.Value), node), this);
            return result;
        }

        [Requires("Pal.InRegion(newNode) && Pal.InRegion(node) && @this.SpecCount < int.MaxValue")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Pos<LinkedListNode<T>>(@this.SpecNodes, node) < 0 || SpecRing.Owner<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), newNode) != null")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecNodes == SpecRing.InsertAt(Pal.Old(@this.SpecNodes), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node), newNode)")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node), Pal.Old(SpecRing.Item<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), newNode)))")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public void AddBefore(LinkedListNode<T> node, LinkedListNode<T> newNode)
        {
            ValidateNode(node);
            ValidateNewNode(newNode);
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, node, this);
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, newNode, this);
            SpecRing.Neighbours<LinkedListNode<T>>(h0.Value, head, count, node);
            SpecRing.Ends<LinkedListNode<T>>(h0.Value, head, count);
            InternalInsertNodeBefore(node, newNode);
            Ghost<SpecHeap<LinkedListNode<T>>> h1 = Pal.Heap<LinkedListNode<T>>();
            newNode.list = this;
            SpecRing.Reowned<LinkedListNode<T>>(h1.Value, Pal.Heap<LinkedListNode<T>>(), head, count, newNode);
            if (node == head)
            {
                SpecRing.Rotated<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, n0.Value, SpecRing.Nodes<LinkedListNode<T>>(h0.Value, hd0.Value, n0.Value), newNode);
                head = newNode;
            }
            SpecRing.Reattached<LinkedListNode<T>, LinkedList<T>>(h0.Value, h1.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, head, newNode, SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(h0.Value, hd0.Value, n0.Value), node), this);
        }

        [Requires("@this.SpecCount < int.MaxValue")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecNodes == SpecRing.InsertAt(Pal.Old(@this.SpecNodes), 0, Result)")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), 0, value)")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public LinkedListNode<T> AddFirst(T value)
        {
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            LinkedListNode<T> result = new LinkedListNode<T>(this, value);
            Ghost<SpecHeap<LinkedListNode<T>>> ha = Pal.Heap<LinkedListNode<T>>();
            SpecRing.Allocated<LinkedListNode<T>>(h0.Value, ha.Value, head, count, result);
            if (head == null)
            {
                InternalInsertNodeToEmptyList(result);
            }
            else
            {
                SpecRing.InsHead<LinkedListNode<T>>(ha.Value, head, count);
                InternalInsertNodeBefore(head, result);
                SpecRing.Rotated<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, n0.Value, SpecRing.Nodes<LinkedListNode<T>>(h0.Value, hd0.Value, n0.Value), result);
                head = result;
            }
            SpecRing.Adopted<LinkedListNode<T>, LinkedList<T>>(h0.Value, ha.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, head, result, 0, this);
            return result;
        }

        [Requires("Pal.InRegion(node) && @this.SpecCount < int.MaxValue")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Owner<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), node) != null")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecNodes == SpecRing.InsertAt(Pal.Old(@this.SpecNodes), 0, node)")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), 0, Pal.Old(SpecRing.Item<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), node)))")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public void AddFirst(LinkedListNode<T> node)
        {
            ValidateNewNode(node);
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, node, this);

            if (head == null)
            {
                InternalInsertNodeToEmptyList(node);
            }
            else
            {
                SpecRing.InsHead<LinkedListNode<T>>(h0.Value, head, count);
                InternalInsertNodeBefore(head, node);
                SpecRing.Rotated<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, n0.Value, SpecRing.Nodes<LinkedListNode<T>>(h0.Value, hd0.Value, n0.Value), node);
                head = node;
            }
            Ghost<SpecHeap<LinkedListNode<T>>> h1 = Pal.Heap<LinkedListNode<T>>();
            node.list = this;
            SpecRing.Reowned<LinkedListNode<T>>(h1.Value, Pal.Heap<LinkedListNode<T>>(), head, count, node);
            SpecRing.Reattached<LinkedListNode<T>, LinkedList<T>>(h0.Value, h1.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, head, node, 0, this);
        }

        [Requires("@this.SpecCount < int.MaxValue")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecNodes == SpecRing.InsertAt(Pal.Old(@this.SpecNodes), Pal.Old(@this.SpecCount), Result)")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), Pal.Old(@this.SpecCount), value)")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public LinkedListNode<T> AddLast(T value)
        {
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            LinkedListNode<T> result = new LinkedListNode<T>(this, value);
            Ghost<SpecHeap<LinkedListNode<T>>> ha = Pal.Heap<LinkedListNode<T>>();
            SpecRing.Allocated<LinkedListNode<T>>(h0.Value, ha.Value, head, count, result);
            if (head == null)
            {
                InternalInsertNodeToEmptyList(result);
            }
            else
            {
                SpecRing.InsHead<LinkedListNode<T>>(ha.Value, head, count);
                InternalInsertNodeBefore(head, result);
            }
            SpecRing.Adopted<LinkedListNode<T>, LinkedList<T>>(h0.Value, ha.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, head, result, n0.Value, this);
            return result;
        }

        [Requires("Pal.InRegion(node) && @this.SpecCount < int.MaxValue")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Owner<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), node) != null")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
        [Ensures("@this.SpecNodes == SpecRing.InsertAt(Pal.Old(@this.SpecNodes), Pal.Old(@this.SpecCount), node)")]
        [Ensures("@this.SpecItems == SpecRing.InsertAt(Pal.Old(@this.SpecItems), Pal.Old(@this.SpecCount), Pal.Old(SpecRing.Item<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), node)))")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public void AddLast(LinkedListNode<T> node)
        {
            ValidateNewNode(node);
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, node, this);

            if (head == null)
            {
                InternalInsertNodeToEmptyList(node);
            }
            else
            {
                SpecRing.InsHead<LinkedListNode<T>>(h0.Value, head, count);
                InternalInsertNodeBefore(head, node);
            }
            Ghost<SpecHeap<LinkedListNode<T>>> h1 = Pal.Heap<LinkedListNode<T>>();
            node.list = this;
            SpecRing.Reowned<LinkedListNode<T>>(h1.Value, Pal.Heap<LinkedListNode<T>>(), head, count, node);
            SpecRing.Reattached<LinkedListNode<T>, LinkedList<T>>(h0.Value, h1.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, head, node, n0.Value, this);
        }

        [Ensures("@this.SpecCount == 0")]
        [Ensures("SpecRing.Cleared<LinkedListNode<T>>(Pal.Old(Pal.Heap<LinkedListNode<T>>()), Pal.Heap<LinkedListNode<T>>(), Pal.Old(@this.SpecNodes), Pal.Old(@this.SpecCount))")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public void Clear()
        {
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            SpecRing.ClearStart<LinkedListNode<T>>(h0.Value, head, count);
            LinkedListNode<T>? current = head;
            while (current != null)
            {
                Pal.Invariant(SpecRing.Ring<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, this));
                Pal.Invariant(current == null || SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(h0.Value, head, count), current) >= 0);
                Pal.Invariant(SpecRing.Cleared<LinkedListNode<T>>(h0.Value, Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(h0.Value, head, count), current == null ? count : SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(h0.Value, head, count), current)));
                Pal.Decreases(current == null ? 0 : count - SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(h0.Value, head, count), current));
                LinkedListNode<T> temp = current;
                SpecRing.ClearNext<LinkedListNode<T>, LinkedList<T>>(h0.Value, Pal.Heap<LinkedListNode<T>>(), head, count, current, this);
                current = current.Next;
                Ghost<SpecHeap<LinkedListNode<T>>> h1 = Pal.Heap<LinkedListNode<T>>();
                temp.Invalidate();
                SpecRing.ClearStep<LinkedListNode<T>>(h0.Value, h1.Value, Pal.Heap<LinkedListNode<T>>(), head, count, temp);
            }
            SpecRing.ClearDone<LinkedListNode<T>, LinkedList<T>>(h0.Value, Pal.Heap<LinkedListNode<T>>(), head, count, this);

            head = null;
            count = 0;
            version++;
        }

        [Ensures("Result == (SpecRing.IndexOf<T>(@this.SpecItems, value) >= 0)")]
        public bool Contains(T value)
        {
            return Find(value) != null;
        }

        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index > Pal.Contents(array).Length")]
        [Throws(typeof(ArgumentException), "Pal.Contents(array).Length - index < @this.SpecCount")]
        [Ensures("0 <= index && index + @this.SpecCount <= Pal.Contents(array).Length && Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.SpecCount, @this.SpecItems)")]
        public void CopyTo(T[] array, int index)
        {
            Ghost<SpecInt> index0 = (SpecInt)index;
            ArgumentNullException.ThrowIfNull(array);

            ArgumentOutOfRangeException.ThrowIfNegative(index);

            if (index > array.Length)
            {
                throw new ArgumentOutOfRangeException(nameof(index), index, SR.ArgumentOutOfRange_BiggerThanCollection);
            }

            if (array.Length - index < Count)
            {
                throw new ArgumentException(SR.Arg_InsufficientSpace);
            }

            LinkedListNode<T>? node = head;
            SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
            if (node != null)
            {
                do
                {
                    Pal.Invariant(Pal.Implies(!Pal.Broke(), Pal.InRegion(node) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node) >= 0 && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node) == index - index0.Value));
                    Pal.Invariant(Pal.Implies(Pal.Broke(), index - index0.Value == count));
                    Pal.Invariant(0 <= index0.Value && index0.Value <= index && index - index0.Value <= count && index0.Value + count <= Pal.Contents(array).Length &&
                                  Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index0.Value, index, Pal.Slice(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), 0, index - index0.Value)));
                    Pal.Decreases(count - (index - index0.Value));
                    SpecRing.Neighbours<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, node!);
                    SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
                    array[index++] = node!.item;
                    node = node.next;
                } while (node != head);
            }
        }

        [Ensures("SpecRing.IndexOf<T>(@this.SpecItems, value) < 0 ? Result == null : Result != null && Result == @this.SpecNodes[SpecRing.IndexOf<T>(@this.SpecItems, value)]")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecNodes == Pal.Old(@this.SpecNodes) && @this.SpecItems == Pal.Old(@this.SpecItems) && @this.SpecVersion == Pal.Old(@this.SpecVersion)")]
        public LinkedListNode<T>? Find(T value)
        {
            LinkedListNode<T>? node = head;
            EqualityComparer<T> c = EqualityComparer<T>.Default;
            SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
            SpecRing.FindStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, 0);
            if (node != null)
            {
                if (value != null)
                {
                    do
                    {
                        Pal.Invariant(Pal.Implies(!Pal.Broke(), !Pal.Returned() && Pal.InRegion(node) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node) >= 0 && SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) == SpecRing.IndexFrom<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node))));
                        Pal.Invariant(Pal.Implies(Pal.Broke(), Pal.Returned() ? Pal.Result<LinkedListNode<T>?>() != null && 0 <= SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) && SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) < count && Pal.Result<LinkedListNode<T>?>() == SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)[SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value)] : SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) < 0));
                        Pal.Decreases(count - SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node));
                        Ghost<SpecInt> i = SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node);
                        SpecRing.Neighbours<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, node!);
                        SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
                        SpecRing.FindStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, i.Value);
                        SpecRing.FindStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, i.Value + 1);
                        if (c.Equals(node!.item, value))
                        {
                            return node;
                        }
                        node = node.next;
                    } while (node != head);
                }
                else
                {
                    do
                    {
                        Pal.Invariant(Pal.Implies(!Pal.Broke(), !Pal.Returned() && Pal.InRegion(node) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node) >= 0 && SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) == SpecRing.IndexFrom<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node))));
                        Pal.Invariant(Pal.Implies(Pal.Broke(), Pal.Returned() ? Pal.Result<LinkedListNode<T>?>() != null && 0 <= SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) && SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) < count && Pal.Result<LinkedListNode<T>?>() == SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)[SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value)] : SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) < 0));
                        Pal.Decreases(count - SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node));
                        Ghost<SpecInt> i = SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node);
                        SpecRing.Neighbours<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, node!);
                        SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
                        SpecRing.FindStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, i.Value);
                        SpecRing.FindStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, i.Value + 1);
                        if (node!.item == null)
                        {
                            return node;
                        }
                        node = node.next;
                    } while (node != head);
                }
            }
            return null;
        }

        [Ensures("SpecRing.LastIndexOf<T>(@this.SpecItems, value) < 0 ? Result == null : Result != null && Result == @this.SpecNodes[SpecRing.LastIndexOf<T>(@this.SpecItems, value)]")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecNodes == Pal.Old(@this.SpecNodes) && @this.SpecItems == Pal.Old(@this.SpecItems) && @this.SpecVersion == Pal.Old(@this.SpecVersion)")]
        public LinkedListNode<T>? FindLast(T value)
        {
            SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
            SpecRing.LastStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, count - 1);
            if (head == null) return null;

            LinkedListNode<T>? last = head.prev;
            LinkedListNode<T>? node = last;
            EqualityComparer<T> c = EqualityComparer<T>.Default;
            if (node != null)
            {
                if (value != null)
                {
                    do
                    {
                        Pal.Invariant(Pal.Implies(!Pal.Broke(), !Pal.Returned() && Pal.InRegion(node) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node) >= 0 && SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) == SpecRing.LastFrom<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node))));
                        Pal.Invariant(Pal.Implies(Pal.Broke(), Pal.Returned() ? Pal.Result<LinkedListNode<T>?>() != null && 0 <= SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) && SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) < count && Pal.Result<LinkedListNode<T>?>() == SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)[SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value)] : SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) < 0));
                        Pal.Decreases(SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node));
                        Ghost<SpecInt> i = SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node);
                        SpecRing.Neighbours<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, node!);
                        SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
                        SpecRing.LastStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, i.Value);
                        SpecRing.LastStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, i.Value - 1);
                        if (c.Equals(node!.item, value))
                        {
                            return node;
                        }

                        node = node.prev;
                    } while (node != last);
                }
                else
                {
                    do
                    {
                        Pal.Invariant(Pal.Implies(!Pal.Broke(), !Pal.Returned() && Pal.InRegion(node) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node) >= 0 && SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) == SpecRing.LastFrom<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node))));
                        Pal.Invariant(Pal.Implies(Pal.Broke(), Pal.Returned() ? Pal.Result<LinkedListNode<T>?>() != null && 0 <= SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) && SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) < count && Pal.Result<LinkedListNode<T>?>() == SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)[SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value)] : SpecRing.LastIndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value) < 0));
                        Pal.Decreases(SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node));
                        Ghost<SpecInt> i = SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count), node);
                        SpecRing.Neighbours<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, node!);
                        SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
                        SpecRing.LastStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, i.Value);
                        SpecRing.LastStep<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value, i.Value - 1);
                        if (node!.item == null)
                        {
                            return node;
                        }

                        node = node.prev;
                    } while (node != last);
                }
            }
            return null;
        }

        [Ensures("ReferenceEquals(Result._list, @this) && Result._version == @this.SpecVersion && Result._index == 0 && Result._node == (@this.SpecCount == 0 ? null : @this.SpecNodes[0])")]
        public Enumerator GetEnumerator() => new Enumerator(this);

        [Ensures("Pal.Implies(@this.SpecCount != 0, Pal.Exists((LinkedList<T>.Enumerator e) => Pal.Boxes(Result, e) && " +
            "ReferenceEquals(e._list, @this) && e._version == @this.SpecVersion && e._index == 0 && e._node == @this.SpecNodes[0]))")]
        IEnumerator<T> IEnumerable<T>.GetEnumerator() =>
            Count == 0 ? EnumerableHelpers.GetEmptyEnumerator<T>() :
            GetEnumerator();

        [Ensures("Result == (SpecRing.IndexOf<T>(Pal.Old(@this.SpecItems), value) >= 0)")]
        [Ensures("@this.SpecCount == (SpecRing.IndexOf<T>(Pal.Old(@this.SpecItems), value) >= 0 ? Pal.Old(@this.SpecCount) - 1 : Pal.Old(@this.SpecCount))")]
        [Ensures("@this.SpecNodes == (SpecRing.IndexOf<T>(Pal.Old(@this.SpecItems), value) >= 0 ? SpecRing.RemoveAt(Pal.Old(@this.SpecNodes), SpecRing.IndexOf<T>(Pal.Old(@this.SpecItems), value)) : Pal.Old(@this.SpecNodes))")]
        [Ensures("@this.SpecItems == (SpecRing.IndexOf<T>(Pal.Old(@this.SpecItems), value) >= 0 ? SpecRing.RemoveAt(Pal.Old(@this.SpecItems), SpecRing.IndexOf<T>(Pal.Old(@this.SpecItems), value)) : Pal.Old(@this.SpecItems))")]
        [Ensures("@this.SpecVersion == (SpecRing.IndexOf<T>(Pal.Old(@this.SpecItems), value) >= 0 ? LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion)) : Pal.Old(@this.SpecVersion))")]
        public bool Remove(T value)
        {
            LinkedListNode<T>? node = Find(value);
            SpecRing.At<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, SpecRing.IndexOf<T>(SpecRing.Items<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count)), value));
            if (node != null)
            {
                InternalRemoveNode(node);
                return true;
            }
            return false;
        }

        [Requires("Pal.InRegion(node)")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Pos<LinkedListNode<T>>(@this.SpecNodes, node) < 0")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) - 1")]
        [Ensures("@this.SpecNodes == SpecRing.RemoveAt(Pal.Old(@this.SpecNodes), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node))")]
        [Ensures("@this.SpecItems == SpecRing.RemoveAt(Pal.Old(@this.SpecItems), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node))")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public void Remove(LinkedListNode<T> node)
        {
            ValidateNode(node);
            InternalRemoveNode(node);
        }

        [Throws(typeof(InvalidOperationException), "@this.SpecCount == 0")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) - 1")]
        [Ensures("@this.SpecNodes == SpecRing.RemoveAt(Pal.Old(@this.SpecNodes), 0)")]
        [Ensures("@this.SpecItems == SpecRing.RemoveAt(Pal.Old(@this.SpecItems), 0)")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public void RemoveFirst()
        {
            SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
            if (head == null) { throw new InvalidOperationException(SR.LinkedListEmpty); }
            InternalRemoveNode(head);
        }

        [Throws(typeof(InvalidOperationException), "@this.SpecCount == 0")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) - 1")]
        [Ensures("@this.SpecNodes == SpecRing.RemoveAt(Pal.Old(@this.SpecNodes), Pal.Old(@this.SpecCount) - 1)")]
        [Ensures("@this.SpecItems == SpecRing.RemoveAt(Pal.Old(@this.SpecItems), Pal.Old(@this.SpecCount) - 1)")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        public void RemoveLast()
        {
            SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), head, count);
            if (head == null) { throw new InvalidOperationException(SR.LinkedListEmpty); }
            InternalRemoveNode(head.prev!);
        }

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        [EditorBrowsable(EditorBrowsableState.Never)]
        public virtual void GetObjectData(SerializationInfo info, StreamingContext context)
        {
            ArgumentNullException.ThrowIfNull(info);

            // Customized serialization for LinkedList.
            // We need to do this because it will be too expensive to Serialize each node.
            // This will give us the flexiblility to change internal implementation freely in future.

            info.AddValue(VersionName, version);
            info.AddValue(CountName, count); // this is the length of the bucket array.

            if (count != 0)
            {
                T[] array = new T[count];
                CopyTo(array, 0);
                info.AddValue(ValuesName, array, typeof(T[]));
            }
        }

        public virtual void OnDeserialization(object? sender)
        {
            if (_siInfo == null)
            {
                return; //Somebody had a dependency on this LinkedList and fixed us up before the ObjectManager got to it.
            }

            int realVersion = _siInfo.GetInt32(VersionName);
            int count = _siInfo.GetInt32(CountName);

            if (count != 0)
            {
                T[]? array = (T[]?)_siInfo.GetValue(ValuesName, typeof(T[]));

                if (array == null)
                {
                    throw new SerializationException(SR.Serialization_MissingValues);
                }
                for (int i = 0; i < array.Length; i++)
                {
                    AddLast(array[i]);
                }
            }
            else
            {
                head = null;
            }

            version = realVersion;
            _siInfo = null;
        }

        [Open]
        [Requires("SpecRing.Shape<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.head, @this.count) && @this.count < int.MaxValue")]
        [Requires("Pal.InRegion(node) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.head, @this.count), node) >= 0")]
        [Requires("Pal.InRegion(newNode) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.head, @this.count), newNode) < 0")]
        [Ensures("@this.head == Pal.Old(@this.head) && @this.count == Pal.Old(@this.count) + 1 && Pal.InRegion(newNode)")]
        [Ensures("SpecRing.Shape<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.head, @this.count) && SpecRing.ViewsKept<LinkedListNode<T>>(Pal.Old(Pal.Heap<LinkedListNode<T>>()), Pal.Heap<LinkedListNode<T>>())")]
        [Ensures("SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.head, @this.count) == SpecRing.InsertAt(SpecRing.Nodes<LinkedListNode<T>>(Pal.Old(Pal.Heap<LinkedListNode<T>>()), Pal.Old(@this.head), Pal.Old(@this.count)), SpecRing.InsIndex<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Old(Pal.Heap<LinkedListNode<T>>()), Pal.Old(@this.head), Pal.Old(@this.count)), node), newNode)")]
        [Ensures("@this.version == LinkedList<T>.Bumped(Pal.Old(@this.version))")]
        private void InternalInsertNodeBefore(LinkedListNode<T> node, LinkedListNode<T> newNode)
        {
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            SpecRing.Neighbours<LinkedListNode<T>>(h0.Value, head, count, node);
            newNode.next = node;
            newNode.prev = node.prev;
            Ghost<SpecHeap<LinkedListNode<T>>> h1 = Pal.Heap<LinkedListNode<T>>();
            node.prev!.next = newNode;
            Ghost<SpecHeap<LinkedListNode<T>>> h2 = Pal.Heap<LinkedListNode<T>>();
            node.prev = newNode;
            SpecRing.Inserted<LinkedListNode<T>>(h0.Value, h1.Value, h2.Value, Pal.Heap<LinkedListNode<T>>(), head, count, node, newNode);
            version++;
            count++;
        }

        [Open]
        [Requires("@this.head == null && @this.count == 0 && Pal.InRegion(newNode)")]
        [Ensures("@this.head == newNode && @this.count == 1 && Pal.InRegion(newNode)")]
        [Ensures("SpecRing.Shape<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.head, @this.count) && SpecRing.ViewsKept<LinkedListNode<T>>(Pal.Old(Pal.Heap<LinkedListNode<T>>()), Pal.Heap<LinkedListNode<T>>())")]
        [Ensures("SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.head, @this.count) == SpecRing.InsertAt(SpecRing.Nodes<LinkedListNode<T>>(Pal.Old(Pal.Heap<LinkedListNode<T>>()), Pal.Old(@this.head), Pal.Old(@this.count)), 0, newNode)")]
        [Ensures("@this.version == LinkedList<T>.Bumped(Pal.Old(@this.version))")]
        private void InternalInsertNodeToEmptyList(LinkedListNode<T> newNode)
        {
            Debug.Assert(head == null && count == 0, "LinkedList must be empty when this method is called!");
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            newNode.next = newNode;
            newNode.prev = newNode;
            SpecRing.Single<LinkedListNode<T>>(h0.Value, Pal.Heap<LinkedListNode<T>>(), head, count, newNode);
            head = newNode;
            version++;
            count++;
        }

        [Requires("Pal.InRegion(node) && SpecRing.Pos<LinkedListNode<T>>(@this.SpecNodes, node) >= 0")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) - 1")]
        [Ensures("@this.SpecNodes == SpecRing.RemoveAt(Pal.Old(@this.SpecNodes), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node))")]
        [Ensures("@this.SpecItems == SpecRing.RemoveAt(Pal.Old(@this.SpecItems), SpecRing.Pos<LinkedListNode<T>>(Pal.Old(@this.SpecNodes), node))")]
        [Ensures("@this.SpecVersion == LinkedList<T>.Bumped(Pal.Old(@this.SpecVersion))")]
        internal void InternalRemoveNode(LinkedListNode<T> node)
        {
            Ghost<SpecHeap<LinkedListNode<T>>> h0 = Pal.Heap<LinkedListNode<T>>();
            Ghost<LinkedListNode<T>?> hd0 = head;
            Ghost<SpecInt> n0 = (SpecInt)count;
            SpecRing.Member<LinkedListNode<T>, LinkedList<T>>(h0.Value, head, count, node, this);
            SpecRing.Neighbours<LinkedListNode<T>>(h0.Value, head, count, node);
            Debug.Assert(node.list == this, "Deleting the node from another list!");
            Debug.Assert(head != null, "This method shouldn't be called on empty list!");
            if (node.next == node)
            {
                Debug.Assert(count == 1 && head == node, "this should only be true for a list with only one node");
                head = null;
            }
            else
            {
                node.next!.prev = node.prev;
                node.prev!.next = node.next;
                if (head == node)
                {
                    head = node.next;
                }
            }
            node.Invalidate();
            SpecRing.Removed<LinkedListNode<T>, LinkedList<T>>(h0.Value, Pal.Heap<LinkedListNode<T>>(), hd0.Value, n0.Value, node, head, this);
            count--;
            version++;
        }

        [Requires("Pal.InRegion(node)")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Owner<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), node) != null")]
        [Ensures("SpecRing.Owner<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), node) == null")]
        internal static void ValidateNewNode(LinkedListNode<T> node)
        {
            ArgumentNullException.ThrowIfNull(node);

            if (node.list != null)
            {
                throw new InvalidOperationException(SR.LinkedListNodeIsAttached);
            }
        }

        [Requires("Pal.InRegion(node)")]
        [Throws(typeof(InvalidOperationException), "SpecRing.Pos<LinkedListNode<T>>(@this.SpecNodes, node) < 0")]
        [Ensures("SpecRing.Pos<LinkedListNode<T>>(@this.SpecNodes, node) >= 0")]
        internal void ValidateNode(LinkedListNode<T> node)
        {
            SpecRing.Owns<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, node, this);
            ArgumentNullException.ThrowIfNull(node);

            if (node.list != this)
            {
                throw new InvalidOperationException(SR.ExternalLinkedListNode);
            }
        }

        bool ICollection.IsSynchronized
        {
            get { return false; }
        }

        object ICollection.SyncRoot => this;

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

            ArgumentOutOfRangeException.ThrowIfNegative(index);

            if (array.Length - index < Count)
            {
                throw new ArgumentException(SR.Arg_InsufficientSpace);
            }

            T[]? tArray = array as T[];
            if (tArray != null)
            {
                CopyTo(tArray, index);
            }
            else
            {
                // No need to use reflection to verify that the types are compatible because it isn't 100% correct and we can rely
                // on the runtime validation during the cast that happens below (i.e. we will get an ArrayTypeMismatchException).
                object?[]? objects = array as object[];
                if (objects == null)
                {
                    throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                }
                LinkedListNode<T>? node = head;
                try
                {
                    if (node != null)
                    {
                        do
                        {
                            objects[index++] = node!.item;
                            node = node.next;
                        } while (node != head);
                    }
                }
                catch (ArrayTypeMismatchException)
                {
                    throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                }
            }
        }

        IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<T>)this).GetEnumerator();

        public struct Enumerator : IEnumerator<T>, IEnumerator, ISerializable, IDeserializationCallback
        {
            private readonly LinkedList<T> _list;
            private LinkedListNode<T>? _node;
            private readonly int _version;
            private T? _current;
            private int _index;

            [Ensures("ReferenceEquals(@this._list, list) && @this._version == list.SpecVersion && @this._index == 0 && @this._node == (list.SpecCount == 0 ? null : list.SpecNodes[0])")]
            internal Enumerator(LinkedList<T> list)
            {
                _list = list;
                _version = list.version;
                _node = list.head;
                _current = default;
                _index = 0;
            }

            [Ensures("Pal.Same(Result, @this._current)")]
            public T Current => _current!;

            [Requires("@this._list.SpecCount < int.MaxValue")]
            [Throws(typeof(InvalidOperationException), "@this._index == 0 || @this._index == @this._list.SpecCount + 1")]
            [Ensures("Pal.Boxes(Result, @this._current)")]
            object? IEnumerator.Current
            {
                get
                {
                    if (_index == 0 || (_index == _list.Count + 1))
                    {
                        throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                    }

                    return Current;
                }
            }

            [Requires("@this._list.SpecCount < int.MaxValue")]
            [Requires("Pal.Implies(@this._version == @this._list.SpecVersion, 0 <= @this._index && @this._index <= @this._list.SpecCount + 1 && @this._node == (@this._index < @this._list.SpecCount ? @this._list.SpecNodes[@this._index] : null))")]
            [Throws(typeof(InvalidOperationException), "@this._version != @this._list.SpecVersion")]
            [Ensures("@this._version == @this._list.SpecVersion")]
            [Ensures("Result == (Pal.Old(@this._index) < @this._list.SpecCount)")]
            [Ensures("Pal.Implies(Result, @this._index == Pal.Old(@this._index) + 1 && Pal.Same(@this._current, @this._list.SpecItems[Pal.Old(@this._index)]))")]
            [Ensures("Pal.Implies(!Result, @this._index == @this._list.SpecCount + 1)")]
            [Ensures("Pal.Implies(@this._version == @this._list.SpecVersion, 0 <= @this._index && @this._index <= @this._list.SpecCount + 1 && @this._node == (@this._index < @this._list.SpecCount ? @this._list.SpecNodes[@this._index] : null))")]
            public bool MoveNext()
            {
                if (_version != _list.version)
                {
                    throw new InvalidOperationException(SR.InvalidOperation_EnumFailedVersion);
                }

                SpecRing.At<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), _list.head, _list.count, _index);
                if (_node == null)
                {
                    _index = _list.Count + 1;
                    return false;
                }

                SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), _list.head, _list.count);
                SpecRing.Neighbours<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), _list.head, _list.count, _node);
                ++_index;
                _current = _node.item;
                _node = _node.next;
                if (_node == _list.head)
                {
                    _node = null;
                }
                return true;
            }

            [Throws(typeof(InvalidOperationException), "@this._version != @this._list.SpecVersion")]
            [Ensures("@this._version == @this._list.SpecVersion && @this._index == 0 && @this._node == (@this._list.SpecCount == 0 ? null : @this._list.SpecNodes[0])")]
            void IEnumerator.Reset()
            {
                if (_version != _list.version)
                {
                    throw new InvalidOperationException(SR.InvalidOperation_EnumFailedVersion);
                }

                SpecRing.Ends<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), _list.head, _list.count);
                _current = default;
                _node = _list.head;
                _index = 0;
            }

            [Ensures("true")]
            public void Dispose()
            {
            }

            void ISerializable.GetObjectData(SerializationInfo info, StreamingContext context)
            {
                throw new PlatformNotSupportedException();
            }

            void IDeserializationCallback.OnDeserialization(object? sender)
            {
                throw new PlatformNotSupportedException();
            }
        }
    }

    // Note following class is not serializable since we customized the serialization of LinkedList.
    [Region(Cyclic = true)]
    public sealed class LinkedListNode<T>
    {
        internal LinkedList<T>? list;
        internal LinkedListNode<T>? next;
        internal LinkedListNode<T>? prev;
        internal T item;

        [Model]
        private (T, LinkedList<T>?) View => (item, list);

        public LinkedListNode(T value)
        {
            item = value;
        }

        internal LinkedListNode(LinkedList<T> list, T value)
        {
            this.list = list;
            item = value;
        }

        public LinkedList<T>? List
        {
            get { return list; }
        }

        [Requires("Pal.InRegion(@this)")]
        [Ensures("Result == SpecRing.Succ<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this)")]
        [Ensures("Pal.Implies(SpecRing.Shape<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count), @this) >= 0, " +
                 "Result == (SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count), @this) + 1 < @this.list!.count ? SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count)[SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count), @this) + 1] : null))")]
        public LinkedListNode<T>? Next
        {
            get { return next == null || next == list!.head ? null : next; }
        }

        [Requires("Pal.InRegion(@this)")]
        [Ensures("Result == SpecRing.Pred<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this)")]
        [Ensures("Pal.Implies(SpecRing.Shape<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count) && SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count), @this) >= 0, " +
                 "Result == (SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count), @this) > 0 ? SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count)[SpecRing.Pos<LinkedListNode<T>>(SpecRing.Nodes<LinkedListNode<T>>(Pal.Heap<LinkedListNode<T>>(), @this.list!.head, @this.list!.count), @this) - 1] : null))")]
        public LinkedListNode<T>? Previous
        {
            get { return prev == null || this == list!.head ? null : prev; }
        }

        public T Value
        {
            [Requires("Pal.InRegion(@this)")]
            [Ensures("Pal.Same(Result, SpecRing.Item<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), @this))")]
            get { return item; }
            [Requires("Pal.InRegion(@this)")]
            [Ensures("Pal.InRegion(@this) && Pal.Same(SpecRing.Item<LinkedListNode<T>, T>(Pal.Heap<LinkedListNode<T>>(), @this), value)")]
            set { item = value; }
        }

        /// <summary>Gets a reference to the value held by the node.</summary>
        public ref T ValueRef => ref item;

        [Requires("Pal.InRegion(@this)")]
        [Ensures("SpecRing.Detached<LinkedListNode<T>>(Pal.Old(Pal.Heap<LinkedListNode<T>>()), Pal.Heap<LinkedListNode<T>>(), @this)")]
        internal void Invalidate()
        {
            list = null;
            next = null;
            prev = null;
        }
    }
}
