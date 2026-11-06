// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.ComponentModel;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Numerics;
using System.Runtime.Serialization;
using Interlocked = System.Threading.Interlocked;
using PalLang;

namespace System.Collections.Generic
{
    // A binary search tree is a red-black tree if it satisfies the following red-black properties:
    // 1. Every node is either red or black
    // 2. Every leaf (nil node) is black
    // 3. If a node is red, the both its children are black
    // 4. Every simple path from a node to a descendant leaf contains the same number of black nodes
    //
    // The basic idea of a red-black tree is to represent 2-3-4 trees as standard BSTs but to add one extra bit of information
    // per node to encode 3-nodes and 4-nodes.
    // 4-nodes will be represented as:   B
    //                                 R   R
    //
    // 3 -node will be represented as:   B     or     B
    //                                 R   B        B   R
    //
    // For a detailed description of the algorithm, take a look at "Algorithms" by Robert Sedgewick.

    [SpecType("Pulse.Lib.CSharp.SearchTree.node_color")]
    internal enum NodeColor : byte
    {
        Black,
        Red
    }

    internal delegate bool TreeWalkPredicate<T>(SortedSet<T>.Node node);

    [SpecType("Pulse.Lib.CSharp.SearchTree.tree_rotation")]
    internal enum TreeRotation : byte
    {
        [SpecCase("Pulse.Lib.CSharp.SearchTree.RotLeft")]
        Left,
        [SpecCase("Pulse.Lib.CSharp.SearchTree.RotLeftRight")]
        LeftRight,
        [SpecCase("Pulse.Lib.CSharp.SearchTree.RotRight")]
        Right,
        [SpecCase("Pulse.Lib.CSharp.SearchTree.RotRightLeft")]
        RightLeft
    }

    /// <summary>The abstract state of a <see cref="SortedSet{T}"/>.</summary>
    [Spec]
    public struct SortedSetModel<T>
    {
        public SpecTree<(T, bool)> Tree;
        public IComparer<T> Comparer;
        public SpecInt Count;
        public SpecInt Version;
    }

    [DebuggerTypeProxy(typeof(ICollectionDebugView<>))]
    [DebuggerDisplay("Count = {Count}")]
    [Serializable]
    [System.Runtime.CompilerServices.TypeForwardedFrom("System, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    public partial class SortedSet<T> : ISet<T>, ICollection<T>, ICollection, IReadOnlyCollection<T>, IReadOnlySet<T>, ISerializable, IDeserializationCallback
    {
        #region Local variables/constants

        private Node? root;
        private IComparer<T> comparer = default!;
        private int count;
        [Wrapping] private int version;

        [Refine("Pal.StrictlySorted(Result.Comparer, SpecSearchTree.Keys(Result.Tree))")]
        [Refine("SpecSearchTree.IsRedBlack(Result.Tree)")]
        [Refine("Result.Count == Result.Tree.Size")]
        [Model]
        private SortedSetModel<T> Model => new SortedSetModel<T>
        {
            Tree = Pal.Tree<(T, bool)>(root),
            Comparer = comparer,
            Count = count,
            Version = version,
        };

        [Spec]
        public SpecInt SpecCount => Model.Count;

        [Spec]
        public IComparer<T> SpecComparer => Model.Comparer;

        [Spec]
        public SpecInt SpecVersion => Model.Version;

        /// <summary>The red-black tree, each node seen as its item and whether it is red.</summary>
        [Spec]
        public SpecTree<(T, bool)> SpecNodes => Model.Tree;

        /// <summary>The set: the items in order, strictly sorted under <see cref="SpecComparer"/>.</summary>
        [Spec]
        public Seq<T> SpecItems => SpecSearchTree.Keys(Model.Tree);

        private SerializationInfo? siInfo; // A temporary variable which we need during deserialization.

        private const string ComparerName = "Comparer"; // Do not rename (binary serialization)
        private const string CountName = "Count"; // Do not rename (binary serialization)
        private const string ItemsName = "Items"; // Do not rename (binary serialization)
        private const string VersionName = "Version"; // Do not rename (binary serialization)

        internal const int StackAllocThreshold = 100;

        #endregion

        #region Constructors

        [Ensures("@this.SpecItems.Length == 0")]
        [Ensures("@this.SpecComparer == Comparer<T>.Default")]
        public SortedSet()
        {
            comparer = Comparer<T>.Default;
        }

        [Ensures("@this.SpecItems.Length == 0")]
        public SortedSet(IComparer<T>? comparer)
        {
            this.comparer = comparer ?? Comparer<T>.Default;
        }


        public SortedSet(IEnumerable<T> collection) : this(collection, Comparer<T>.Default) { }

        public SortedSet(IEnumerable<T> collection, IComparer<T>? comparer)
            : this(comparer)
        {
            ArgumentNullException.ThrowIfNull(collection);

            // These are explicit type checks in the mold of HashSet. It would have worked better with
            // something like an ISorted<T> interface. (We could make this work for SortedList.Keys, etc.)
            SortedSet<T>? sortedSet = collection as SortedSet<T>;
            if (sortedSet != null && !(sortedSet is TreeSubSet) && HasEqualComparer(sortedSet))
            {
                if (sortedSet.Count > 0)
                {
                    Debug.Assert(sortedSet.root != null);
                    this.count = sortedSet.count;
                    root = sortedSet.root.DeepClone(this.count);
                }
                return;
            }

            int count;
            T[] elements = EnumerableHelpers.ToArray(collection, out count);
            if (count > 0)
            {
                // If `comparer` is null, sets it to Comparer<T>.Default. We checked for this condition in the IComparer<T> constructor.
                // Array.Sort handles null comparers, but we need this later when we use `comparer.Compare` directly.
                comparer = this.comparer;
                Array.Sort(elements, 0, count, comparer);

                // Overwrite duplicates while shifting the distinct elements towards
                // the front of the array.
                int index = 1;
                for (int i = 1; i < count; i++)
                {
                    if (comparer.Compare(elements[i], elements[i - 1]) != 0)
                    {
                        elements[index++] = elements[i];
                    }
                }

                count = index;
                root = ConstructRootFromSortedArray(elements, 0, count - 1, null);
                this.count = count;
            }
        }

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        [EditorBrowsable(EditorBrowsableState.Never)]
        protected SortedSet(SerializationInfo info, StreamingContext context) => siInfo = info;

        #endregion

        #region Bulk operation helpers

        private void AddAllElements(IEnumerable<T> collection)
        {
            foreach (T item in collection)
            {
                if (!Contains(item))
                {
                    Add(item);
                }
            }
        }

        private void RemoveAllElements(IEnumerable<T> collection)
        {
            T? min = Min;
            T? max = Max;
            foreach (T item in collection)
            {
                if (!(comparer.Compare(item, min) < 0 || comparer.Compare(item, max) > 0) && Contains(item))
                {
                    Remove(item);
                }
            }
        }

        private bool ContainsAllElements(IEnumerable<T> collection)
        {
            foreach (T item in collection)
            {
                if (!Contains(item))
                {
                    return false;
                }
            }

            return true;
        }

        /// <summary>
        /// Does an in-order tree walk and calls the delegate for each node.
        /// </summary>
        /// <param name="action">
        /// The delegate to invoke on each node.
        /// If the delegate returns <c>false</c>, the walk is stopped.
        /// </param>
        /// <returns><c>true</c> if the entire tree has been walked; otherwise, <c>false</c>.</returns>
        // pal: R27.39. `action` is called on the nodes in order, and the walk stops at the
        // first false: what it was called on, and what it returned, is the trace the
        // caller's protocol is kept over. Overrides (TreeSubSet) are not verified.
        [Ensures("SpecWalk.Walked(@this.SpecItems, Pal.Trace<(T, bool), bool>(action), Result)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Rlimit(8)]
        [Wrapping]
        internal virtual bool InOrderTreeWalk([Callback] TreeWalkPredicate<T> action)
        {
            if (root == null)
            {
                return true;
            }

            // The maximum height of a red-black tree is 2 * log2(n+1).
            // See page 264 of "Introduction to algorithms" by Thomas H. Cormen
            // Note: It's not strictly necessary to provide the stack capacity, but we don't
            // want the stack to unnecessarily allocate arrays as it grows.

            var stack = new Stack<Node>(2 * (int)Log2(Count + 1));
            Node? current = root;
            SpecWalk.Empty<Node, T>(false, Pal.Heap<Node>(), stack.Items);

            while (current != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                Pal.Invariant(Pal.WellFormed(current) && SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), stack.Items) &&
                              SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                              Pal.Trace<(T, bool), bool>(action).Length == 0 &&
                              Pal.Concat(SpecWalk.Keys(false, Pal.Tree<(T, bool)>(current)),
                                         SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items)) ==
                              SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)));
                SpecWalk.Descend<Node, T>(false, Pal.Heap<Node>(), stack.Items, current);
                Pal.Assert(stack.Items.Length < count);
                stack.Push(current);
                current = current.Left;
            }

            while (stack.Count != 0)
            {
                Pal.Decreases(count - Pal.Trace<(T, bool), bool>(action).Length);
                Pal.Invariant(SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), stack.Items) &&
                              0 <= Pal.Trace<(T, bool), bool>(action).Length && Pal.Trace<(T, bool), bool>(action).Length <= count &&
                              SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                              (Pal.Returned()
                                  ? !Pal.ReturnValue<bool>() &&
                                    SpecWalk.Walked(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action), false)
                                  : SpecWalk.Visited(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action)) &&
                                    SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items) ==
                                    Pal.Slice(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action).Length, count)));
                SpecWalk.PopAt<Node, T>(false, Pal.Heap<Node>(), stack.Items, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action).Length);
                current = stack.Pop();
                if (!action(current))
                {
                    return false;
                }

                Node? node = current.Right;
                while (node != null)
                {
                    Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                    Pal.Invariant(Pal.WellFormed(node) && SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), stack.Items) &&
                                  0 < Pal.Trace<(T, bool), bool>(action).Length && Pal.Trace<(T, bool), bool>(action).Length <= count &&
                                  SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                                  SpecWalk.Visited(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action)) &&
                                  Pal.Concat(SpecWalk.Keys(false, Pal.Tree<(T, bool)>(node)),
                                             SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items)) ==
                                  Pal.Slice(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action).Length, count));
                    SpecWalk.Descend<Node, T>(false, Pal.Heap<Node>(), stack.Items, node);
                    Pal.Assert(stack.Items.Length < count - Pal.Trace<(T, bool), bool>(action).Length);
                    stack.Push(node);
                    node = node.Left;
                }
            }

            return true;
        }

        /// <summary>
        /// Does a left-to-right breadth-first tree walk and calls the delegate for each node.
        /// </summary>
        /// <param name="action">
        /// The delegate to invoke on each node.
        /// If the delegate returns <c>false</c>, the walk is stopped.
        /// </param>
        /// <returns><c>true</c> if the entire tree has been walked; otherwise, <c>false</c>.</returns>
        // pal: R27.40. `action` is called on the nodes level by level, and the walk stops at
        // the first false: every call is on a distinct member, all calls but the last
        // returned true, and a true result means every member was called on exactly once.
        // Overrides (TreeSubSet) are not verified.
        [Ensures("SpecWalk.BfWalked(@this.SpecItems, Pal.Trace<(T, bool), bool>(action), Result)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Rlimit(20)]
        [Wrapping]
        internal virtual bool BreadthFirstTreeWalk([Callback] TreeWalkPredicate<T> action)
        {
            if (root == null)
            {
                return true;
            }

            var processQueue = new Queue<Node>();
            processQueue.Enqueue(root);
            SpecWalk.BfStart<Node, T, bool>(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action),
                                            SpecWalk.BfPending<Node, T>(Pal.Heap<Node>(), processQueue.Items));

            Node current;
            while (processQueue.Count != 0)
            {
                Pal.Decreases(count - Pal.Trace<(T, bool), bool>(action).Length);
                Pal.Invariant(SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), processQueue.Items) &&
                              0 <= Pal.Trace<(T, bool), bool>(action).Length &&
                              SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)).Length == count &&
                              (Pal.Returned()
                                  ? !Pal.ReturnValue<bool>() &&
                                    SpecWalk.BfWalked(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action), false)
                                  : SpecWalk.BfVisited(SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action),
                                                       SpecWalk.BfPending<Node, T>(Pal.Heap<Node>(), processQueue.Items))));
                Ghost<Seq<Node>> q0 = processQueue.Items;
                SpecWalk.BfDequeue<Node, T, bool>(Pal.Heap<Node>(), q0.Value,
                                                  SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)), Pal.Trace<(T, bool), bool>(action));
                current = processQueue.Dequeue();
                Pal.Assert(Pal.Trace<(T, bool), bool>(action).Length < int.MaxValue);
                if (!action(current))
                {
                    return false;
                }

                Pal.Assert(processQueue.SpecCount < int.MaxValue);
                if (current.Left != null)
                {
                    processQueue.Enqueue(current.Left);
                }
                Pal.Assert(processQueue.SpecCount < int.MaxValue);
                if (current.Right != null)
                {
                    processQueue.Enqueue(current.Right);
                }
                Pal.Assert(processQueue.Items == SpecWalk.BfNext<Node, T>(Pal.Heap<Node>(), q0.Value));
            }

            return true;
        }

        #endregion

        #region Properties

        [Ensures("Result == @this.SpecItems.Length")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public int Count
        {
            get
            {
                VersionCheck(updateCount: true);
                return count;
            }
        }

        [Ensures("Result == @this.SpecComparer")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public IComparer<T> Comparer => comparer;

        bool ICollection<T>.IsReadOnly => false;

        bool ICollection.IsSynchronized => false;

        object ICollection.SyncRoot => this;

        #endregion

        #region Subclass helpers

        // Virtual function for TreeSubSet, which may need to update its count.
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual void VersionCheck(bool updateCount = false) { }
        // Virtual function for TreeSubSet, which may need the count variable of the parent set.
        [Ensures("Result == @this.SpecItems.Length")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual int TotalCount() { return Count; }

        // Virtual function for TreeSubSet, which may need to do range checks.
        [Ensures("Result")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual bool IsWithinRange(T item) => true;

        #endregion

        #region ICollection<T> members

        [Requires("@this.SpecItems.Length < int.MaxValue")]
        [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) < 0)")]
        [Ensures("Pal.Implies(Result, @this.SpecItems == SpecTopDown.Inserted(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item))")]
        [Ensures("Pal.Implies(!Result, @this.SpecItems == Pal.Old(@this.SpecItems))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public bool Add(T item) => AddIfNotPresent(item); // Hack so the implementation can be made virtual

        void ICollection<T>.Add(T item) => Add(item);

        [Requires("@this.SpecItems.Length < int.MaxValue")]
        [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) < 0)")]
        [Ensures("Pal.Implies(Result, @this.SpecItems == SpecTopDown.Inserted(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item))")]
        [Ensures("Pal.Implies(!Result, @this.SpecItems == Pal.Old(@this.SpecItems))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual bool AddIfNotPresent(T item)
        {
            if (root == null)
            {
                // The tree is empty and this is the first item.
                root = new Node(item, NodeColor.Black);
                count = 1;
                version++;
                return true;
            }

            // Search for a node at bottom to insert the new node.
            // If we can guarantee the node we found is not a 4-node, it would be easy to do insertion.
            // We split 4-nodes along the search path.
            Node? current = root;
            Node? parent = null;
            Node? grandParent = null;
            Node? greatGrandParent = null;

            // Even if we don't actually add to the set, we may be altering its structure (by doing rotations and such).
            // So update `_version` to disable any instances of Enumerator/TreeSubSet from working on it.
            version++;

            Ghost<Seq<T>> k0 = SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root));
            SpecTopDown.Start<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root);

            int order = 0;
            while (current != null)
            {
                Pal.Decreases(SpecTopDown.Measure<Node, T>(comparer, item, Pal.Heap<Node>(), root, current));
                Pal.Invariant(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount));
                Pal.Invariant(Pal.Implies(!Pal.Returned(),
                    SpecTopDown.Inv<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, greatGrandParent, order)));
                Pal.Invariant(Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() &&
                    Pal.KeyIndex(comparer, k0.Value, item) >= 0 && Pal.Unshared(root) &&
                    SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root)) == k0.Value &&
                    SpecSearchTree.IsRedBlack(Pal.Tree<(T, bool)>(root)) &&
                    Pal.Tree<(T, bool)>(root).Size == k0.Value.Length));
                SpecTopDown.AtCur<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, greatGrandParent, order);
                Ghost<SpecHeap<Node>> h = Pal.Heap<Node>();
                Ghost<SpecInt> m0 = SpecTopDown.Measure<Node, T>(comparer, item, h.Value, root, current);
                Ghost<int> order0 = order;
                order = comparer.Compare(item, current.Item);
                SpecTopDown.Look<Node, T>(comparer, k0.Value, item, h.Value, root, current, parent, grandParent, greatGrandParent, order0.Value, order);
                if (order == 0)
                {
                    // We could have changed root node to red during the search process.
                    // We need to set it to black before we return.
                    root.ColorBlack();
                    SpecTopDown.Finish<Node, T>(comparer, k0.Value, h.Value, Pal.Heap<Node>(), root);
                    return false;
                }

                // Split a 4-node into two 2-nodes.
                if (current.Is4Node)
                {
                    current.Split4Node();
                    SpecTopDown.Split<Node, T>(comparer, k0.Value, item, h.Value, Pal.Heap<Node>(), root, current, parent, grandParent, greatGrandParent, order0.Value, order);
                    // We could have introduced two consecutive red nodes after split. Fix that by rotation.
                    if (Node.IsNonNullRed(parent))
                    {
                        Ghost<SpecHeap<Node>> h1 = Pal.Heap<Node>();
                        Ghost<Node?> root1 = root;
                        Ghost<Node?> par1 = parent;
                        InsertionBalance(current, ref parent!, grandParent!, greatGrandParent!);
                        SpecTopDown.AfterBalance<Node, T>(comparer, k0.Value, item, h1.Value, Pal.Heap<Node>(), root1.Value, root, current, par1.Value, parent, grandParent, greatGrandParent, order, m0.Value);
                    }
                }

                greatGrandParent = grandParent;
                grandParent = parent;
                parent = current;
                current = (order < 0) ? current.Left : current.Right;
            }

            SpecTopDown.AtEnd<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, parent, grandParent, greatGrandParent, order);
            Ghost<SpecHeap<Node>> hl = Pal.Heap<Node>();
            Ghost<Seq<T>> k1 = SpecTopDown.Inserted(comparer, k0.Value, item);
            Debug.Assert(parent != null);
            // We're ready to insert the new node.
            Node node = new Node(item, NodeColor.Red);
            if (order > 0)
            {
                parent.Right = node;
            }
            else
            {
                parent.Left = node;
            }
            SpecTopDown.LinkedLeaf<Node, T>(comparer, k0.Value, item, hl.Value, Pal.Heap<Node>(), root, node, parent, grandParent, greatGrandParent, order);

            // The new node will be red, so we will need to adjust colors if its parent is also red.
            if (parent.IsRed)
            {
                Ghost<SpecHeap<Node>> h2 = Pal.Heap<Node>();
                Ghost<Node?> root2 = root;
                Ghost<Node?> par2 = parent;
                InsertionBalance(node, ref parent!, grandParent!, greatGrandParent!);
                SpecTopDown.AfterInsertBalance<Node, T>(comparer, k1.Value, h2.Value, Pal.Heap<Node>(), root2.Value, root, node, par2.Value, parent, greatGrandParent);
            }

            // The root node is always black.
            Ghost<SpecHeap<Node>> h3 = Pal.Heap<Node>();
            root.ColorBlack();
            SpecTopDown.FinishOk<Node, T>(comparer, k1.Value, h3.Value, Pal.Heap<Node>(), root);
            ++count;
            return true;
        }

        [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) >= 0)")]
        [Ensures("@this.SpecItems == SpecTopDownRemove.Removed(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public bool Remove(T item) => DoRemove(item); // Hack so the implementation can be made virtual

        [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) >= 0)")]
        [Ensures("@this.SpecItems == SpecTopDownRemove.Removed(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual bool DoRemove(T item)
        {
            if (root == null)
            {
                return false;
            }

            // Search for a node and then find its successor.
            // Then copy the item from the successor to the matching node, and delete the successor.
            // If a node doesn't have a successor, we can replace it with its left child (if not empty),
            // or delete the matching node.
            //
            // In top-down implementation, it is important to make sure the node to be deleted is not a 2-node.
            // Following code will make sure the node on the path is not a 2-node.

            // Even if we don't actually remove from the set, we may be altering its structure (by doing rotations
            // and such). So update our version to disable any enumerators/subsets working on it.
            version++;

            Node? current = root;
            Node? parent = null;
            Node? grandParent = null;
            Node? match = null;
            Node? parentOfMatch = null;
            bool foundMatch = false;
            Ghost<Seq<T>> k0 = SpecSearchTree.Keys(Pal.Tree<(T, bool)>(root));
            SpecTopDownRemove.Start<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root);
            while (current != null)
            {
                Pal.Decreases(SpecTopDownRemove.Measure<Node, T>(Pal.Heap<Node>(), root, current));
                Pal.Invariant(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount));
                Pal.Invariant(SpecTopDownRemove.RInv<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch));
                SpecTopDownRemove.AtCur<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch);
                Ghost<SpecHeap<Node>> h = Pal.Heap<Node>();
                Ghost<SpecInt> m0 = SpecTopDownRemove.Measure<Node, T>(h.Value, root, current);
                if (current.Is2Node)
                {
                    // Fix up 2-node
                    if (parent == null)
                    {
                        // `current` is the root. Mark it red.
                        current.ColorRed();
                        SpecTopDownRemove.FixRoot<Node, T>(comparer, k0.Value, item, h.Value, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value);
                    }
                    else
                    {
                        SpecTopDownRemove.SibPre<Node, T>(comparer, k0.Value, item, h.Value, root, current, parent, grandParent, match, parentOfMatch, foundMatch);
                        Node sibling = parent.GetSibling(current);
                        SpecTopDownRemove.AtSib<Node, T>(comparer, k0.Value, item, h.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch, m0.Value);
                        if (sibling.IsRed)
                        {
                            // If parent is a 3-node, flip the orientation of the red link.
                            // We can achieve this by a single rotation.
                            // This case is converted to one of the other cases below.
                            Debug.Assert(parent.IsBlack);
                            if (parent.Right == sibling)
                            {
                                parent.RotateLeft();
                            }
                            else
                            {
                                parent.RotateRight();
                            }

                            Ghost<SpecHeap<Node>> ha1 = Pal.Heap<Node>();
                            SpecTopDownRemove.AMid<Node, T>(comparer, k0.Value, item, h.Value, ha1.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch);
                            parent.ColorRed();
                            Ghost<SpecHeap<Node>> ha2 = Pal.Heap<Node>();
                            SpecTopDownRemove.ARed<Node, T>(comparer, k0.Value, item, h.Value, ha1.Value, ha2.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch);
                            sibling.ColorBlack(); // The red parent can't have black children.
                            Ghost<SpecHeap<Node>> ha3 = Pal.Heap<Node>();
                            Ghost<Node?> roota = root;
                            // `sibling` becomes the child of `grandParent` or `root` after rotation. Update the link from that node.
                            ReplaceChildOrRoot(grandParent, parent, sibling);
                            SpecTopDownRemove.AEnd<Node, T>(comparer, k0.Value, item, h.Value, ha1.Value, ha2.Value, ha3.Value, Pal.Heap<Node>(), roota.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch);
                            // `sibling` will become the grandparent of `current`.
                            grandParent = sibling;
                            if (parent == match)
                            {
                                parentOfMatch = sibling;
                            }

                            SpecTopDownRemove.MidPre<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value);
                            sibling = parent.GetSibling(current);
                        }

                        SpecTopDownRemove.AtMid<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch, m0.Value);
                        Debug.Assert(Node.IsNonNullBlack(sibling));

                        Ghost<SpecHeap<Node>> hb = Pal.Heap<Node>();
                        if (sibling.Is2Node)
                        {
                            parent.Merge2Nodes();
                            SpecTopDownRemove.Merge<Node, T>(comparer, k0.Value, item, hb.Value, Pal.Heap<Node>(), root, current, parent, grandParent, match, parentOfMatch, sibling, foundMatch, m0.Value);
                        }
                        else
                        {
                            // `current` is a 2-node and `sibling` is either a 3-node or a 4-node.
                            // We can change the color of `current` to red by some rotation.
                            Node newGrandParent = parent.Rotate(parent.GetRotation(current, sibling))!;
                            Ghost<SpecHeap<Node>> hb1 = Pal.Heap<Node>();
                            SpecTopDownRemove.BRot<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);

                            newGrandParent.Color = parent.Color;
                            Ghost<SpecHeap<Node>> hb2 = Pal.Heap<Node>();
                            SpecTopDownRemove.BColW<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, hb2.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
                            parent.ColorBlack();
                            Ghost<SpecHeap<Node>> hb3 = Pal.Heap<Node>();
                            SpecTopDownRemove.BBlk<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, hb2.Value, hb3.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
                            current.ColorRed();
                            Ghost<SpecHeap<Node>> hb4 = Pal.Heap<Node>();
                            SpecTopDownRemove.BCur<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, hb2.Value, hb3.Value, hb4.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
                            Ghost<Node?> rootb = root;

                            ReplaceChildOrRoot(grandParent, parent, newGrandParent);
                            SpecTopDownRemove.BEnd<Node, T>(comparer, k0.Value, item, hb.Value, hb1.Value, hb2.Value, hb3.Value, hb4.Value, Pal.Heap<Node>(), rootb.Value, root, current, parent, grandParent, match, parentOfMatch, sibling, newGrandParent, foundMatch, m0.Value);
                            if (parent == match)
                            {
                                parentOfMatch = newGrandParent;
                            }
                        }
                    }
                }

                SpecTopDownRemove.AtFx<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, match, parentOfMatch, foundMatch, m0.Value);
                // We don't need to compare after we find the match.
                int order = foundMatch ? -1 : comparer.Compare(item, current.Item);
                SpecTopDownRemove.Step<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, current, parent, match, parentOfMatch, foundMatch, m0.Value, order, order == 0, order < 0);
                if (order == 0)
                {
                    // Save the matching node.
                    foundMatch = true;
                    match = current;
                    parentOfMatch = parent;
                }

                grandParent = parent;
                parent = current;
                // If we found a match, continue the search in the right sub-tree.
                current = order < 0 ? current.Left : current.Right;
            }

            SpecTopDownRemove.After<Node, T>(comparer, k0.Value, item, Pal.Heap<Node>(), root, parent, grandParent, match, parentOfMatch, foundMatch);
            Ghost<Seq<T>> k1 = SpecTopDownRemove.Removed(comparer, k0.Value, item);
            // Move successor to the matching node position and replace links.
            if (match != null)
            {
                Ghost<SpecHeap<Node>> hr = Pal.Heap<Node>();
                Ghost<Node?> rootr = root;
                ReplaceNode(match, parentOfMatch!, parent!, grandParent!);
                SpecTopDownRemove.Replaced<Node, T>(comparer, k0.Value, item, hr.Value, Pal.Heap<Node>(), rootr.Value, root, match, parentOfMatch, parent, grandParent);
                --count;
            }

            Ghost<SpecHeap<Node>> hf = Pal.Heap<Node>();
            root?.ColorBlack();
            SpecTopDownRemove.Finish<Node, T>(comparer, k1.Value, hf.Value, Pal.Heap<Node>(), root);
            return foundMatch;
        }

        [Ensures("@this.SpecItems.Length == 0")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public virtual void Clear()
        {
            root = null;
            count = 0;
            ++version;
        }

        [Ensures("Result == (Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public virtual bool Contains(T item) => FindNode(item) != null;

        [Throws(typeof(ArgumentException), "Pal.Contents(array).Length < @this.SpecItems.Length")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), 0, @this.SpecItems.Length, @this.SpecItems)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public void CopyTo(T[] array) => CopyTo(array, 0, Count);

        [Throws(typeof(ArgumentOutOfRangeException), "index < 0")]
        [Throws(typeof(ArgumentException), "Pal.Contents(array).Length - index < @this.SpecItems.Length")]
        [Ensures("0 <= index && Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.SpecItems.Length, @this.SpecItems)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public void CopyTo(T[] array, int index) => CopyTo(array, index, Count);

        // pal: R27.39. The first min(count, Count) items, in order, at `index`.
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || count < 0")]
        [Throws(typeof(ArgumentException), "count > Pal.Contents(array).Length - index")]
        [Ensures("0 <= index && 0 <= count && index + count <= Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("SpecWalk.CopyResult(@this.SpecItems, Pal.Old(Pal.Contents(array)), Pal.Contents(array), index, index + count)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public void CopyTo(T[] array, int index, int count)
        {
            ArgumentNullException.ThrowIfNull(array);

            ArgumentOutOfRangeException.ThrowIfNegative(index);

            ArgumentOutOfRangeException.ThrowIfNegative(count);

            if (count > array.Length - index)
            {
                throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall);
            }

            count += index; // Make `count` the upper bound.
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
                throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall);
            }

            T[]? tarray = array as T[];
            if (tarray != null)
            {
                CopyTo(tarray, index);
            }
            else
            {
                object?[]? objects = array as object[];
                if (objects == null)
                {
                    throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                }

                try
                {
                    InOrderTreeWalk(node =>
                    {
                        objects[index++] = node.Item;
                        return true;
                    });
                }
                catch (ArrayTypeMismatchException)
                {
                    throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                }
            }
        }

        #endregion

        #region IEnumerable<T> members

        [Ensures("ReferenceEquals(Result._tree, @this) && Result._version == @this.SpecVersion && !Result._reverse")]
        [Ensures("SpecWalk.Walkable<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), Result._stack.Items)")]
        [Ensures("SpecWalk.Pending<SortedSet<T>.Node, T>(false, Pal.Heap<SortedSet<T>.Node>(), Result._stack.Items) == @this.SpecItems")]
        public Enumerator GetEnumerator() => new Enumerator(this);

        IEnumerator<T> IEnumerable<T>.GetEnumerator() => GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<T>)this).GetEnumerator();

        #endregion

        #region Tree-specific operations

        // After calling InsertionBalance, we need to make sure `current` and `parent` are up-to-date.
        // It doesn't matter if we keep `grandParent` and `greatGrandParent` up-to-date, because we won't
        // need to split again in the next node.
        // By the time we need to split again, everything will be correctly set.
        [Open]
        [Requires("parent != null")]
        [Requires("SpecTopDown.BalancePre<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this.root, current, parent, grandParent, greatGrandParent)")]
        [Ensures("SpecTopDown.Balanced<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), Pal.Old(@this.root), @this.root, current, Pal.Old(parent), parent, greatGrandParent)")]
        [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
        private void InsertionBalance(Node current, ref Node parent, Node grandParent, [System.Diagnostics.CodeAnalysis.AllowNull] Node greatGrandParent)
        {
            Debug.Assert(parent != null);
            Debug.Assert(grandParent != null);

            Ghost<SpecHeap<Node>> h0 = Pal.Heap<Node>();
            Ghost<Node?> root0 = root;
            Ghost<Node> parent0 = parent;
            SpecTopDown.BalStart<Node, T>(h0.Value, root, current, parent, grandParent, greatGrandParent);
            SpecTopDown.BalGgp<Node, T>(h0.Value, root, current, parent, grandParent, greatGrandParent);
            bool parentIsOnRight = grandParent.Right == parent;
            bool currentIsOnRight = parent.Right == current;
            SpecTopDown.BalRot<Node, T>(h0.Value, root, current, parent, grandParent, greatGrandParent, currentIsOnRight, parentIsOnRight);

            Node newChildOfGreatGrandParent;
            if (parentIsOnRight == currentIsOnRight)
            {
                // Same orientation, single rotation
                newChildOfGreatGrandParent = currentIsOnRight ? grandParent.RotateLeft() : grandParent.RotateRight();
            }
            else
            {
                // Different orientation, double rotation
                newChildOfGreatGrandParent = currentIsOnRight ? grandParent.RotateLeftRight() : grandParent.RotateRightLeft();
                // Current node now becomes the child of `greatGrandParent`
                parent = greatGrandParent;
            }

            Ghost<SpecHeap<Node>> h1 = Pal.Heap<Node>();
            SpecTopDown.BalMid<Node, T>(h0.Value, h1.Value, root0.Value, current, parent0.Value, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);

            // `grandParent` will become a child of either `parent` of `current`.
            grandParent.ColorRed();
            Ghost<SpecHeap<Node>> h2 = Pal.Heap<Node>();
            SpecTopDown.BalRed<Node, T>(h0.Value, h1.Value, h2.Value, root0.Value, current, parent0.Value, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);
            newChildOfGreatGrandParent.ColorBlack();
            Ghost<SpecHeap<Node>> h3 = Pal.Heap<Node>();

            ReplaceChildOrRoot(greatGrandParent, grandParent, newChildOfGreatGrandParent);
            SpecTopDown.BalEnd<Node, T>(h0.Value, h1.Value, h2.Value, h3.Value, Pal.Heap<Node>(), root0.Value, root, current, parent0.Value, parent, grandParent, greatGrandParent, newChildOfGreatGrandParent, currentIsOnRight, parentIsOnRight);
        }

        /// <summary>
        /// Replaces the child of a parent node, or replaces the root if the parent is <c>null</c>.
        /// </summary>
        /// <param name="parent">The (possibly <c>null</c>) parent.</param>
        /// <param name="child">The child node to replace.</param>
        /// <param name="newChild">The node to replace <paramref name="child"/> with.</param>
        [Open]
        [Requires("parent == null || Pal.InRegion(parent)")]
        [Ensures("SpecTopDown.Replaced<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), Pal.Old(@this.root), @this.root, parent, child, newChild)")]
        [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
        private void ReplaceChildOrRoot(Node? parent, Node child, [System.Diagnostics.CodeAnalysis.AllowNull] Node newChild)
        {
            if (parent != null)
            {
                parent.ReplaceChild(child, newChild);
            }
            else
            {
                root = newChild;
            }
        }

        /// <summary>
        /// Replaces the matching node with its successor.
        /// </summary>
        [Open]
        [Requires("SpecTopDownRemove.RnPre<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this.root, match, parentOfMatch, successor, parentOfSuccessor)")]
        [Ensures("SpecTopDownRemove.RnPost<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), Pal.Old(@this.root), @this.root, match)")]
        [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
        private void ReplaceNode(Node match, [System.Diagnostics.CodeAnalysis.AllowNull] Node parentOfMatch, Node successor, [System.Diagnostics.CodeAnalysis.AllowNull] Node parentOfSuccessor)
        {
            Debug.Assert(match != null);

            Ghost<SpecHeap<Node>> h0 = Pal.Heap<Node>();
            Ghost<Node?> root0 = root;
            Ghost<Node> succ0 = successor;
            SpecTopDownRemove.RnStart<Node, T>(h0.Value, root, match, parentOfMatch, successor, parentOfSuccessor);
            if (successor == match)
            {
                // This node has no successor. This can only happen if the right child of the match is null.
                Debug.Assert(match.Right == null);
                SpecTopDownRemove.RnA<Node, T>(h0.Value, root, match, parentOfMatch, successor, parentOfSuccessor);
                successor = match.Left!;
            }
            else
            {
                Debug.Assert(parentOfSuccessor != null);
                Debug.Assert(successor.Left == null);
                Debug.Assert((successor.Right == null && successor.IsRed) || (successor.Right!.IsRed && successor.IsBlack));

                successor.Right?.ColorBlack();
                Ghost<SpecHeap<Node>> h1 = Pal.Heap<Node>();

                if (parentOfSuccessor != match)
                {
                    // Detach the successor from its parent and set its right child.
                    parentOfSuccessor.Left = successor.Right;
                    successor.Right = match.Right;
                }

                successor.Left = match.Left;
                SpecTopDownRemove.RnB<Node, T>(h0.Value, h1.Value, Pal.Heap<Node>(), root0.Value, match, parentOfMatch, successor, parentOfSuccessor);
            }

            Ghost<SpecHeap<Node>> h4 = Pal.Heap<Node>();
            successor?.Color = match.Color;
            Ghost<SpecHeap<Node>> h5 = Pal.Heap<Node>();

            ReplaceChildOrRoot(parentOfMatch, match, successor!);
            SpecTopDownRemove.RnDone<Node, T>(h0.Value, h4.Value, h5.Value, Pal.Heap<Node>(), root0.Value, root, match, parentOfMatch, succ0.Value, parentOfSuccessor, successor);
        }

        [Ensures("(Result != null) == (Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0)")]
        [Ensures("Result == null || Pal.WellFormed(Result) && Pal.Same(SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Result), item), SpecSearchTree.Find(@this.SpecComparer, @this.SpecNodes, item, item))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual Node? FindNode(T item)
        {
            Node? current = root;
            while (current != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.WellFormed(current) &&
                              SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(current), item) ==
                              SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(root), item) &&
                              Pal.Same(SpecSearchTree.Find(comparer, Pal.Tree<(T, bool)>(current), item, item),
                                       SpecSearchTree.Find(comparer, Pal.Tree<(T, bool)>(root), item, item))));
                Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.ReturnValue<Node?>() != null &&
                              SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(root), item) &&
                              Pal.WellFormed(Pal.ReturnValue<Node?>()) &&
                              Pal.Same(SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Pal.ReturnValue<Node?>()), item),
                                       SpecSearchTree.Find(comparer, Pal.Tree<(T, bool)>(root), item, item))));
                int order = comparer.Compare(item, current.Item);
                if (order == 0)
                {
                    return current;
                }

                current = order < 0 ? current.Left : current.Right;
            }

            return null;
        }

        /// <summary>
        /// Searches for an item and returns its zero-based index in this set.
        /// </summary>
        /// <param name="item">The item.</param>
        /// <returns>The item's zero-based index in this set, or -1 if it isn't found.</returns>
        /// <remarks>
        /// <para>
        /// This implementation is based off of http://en.wikipedia.org/wiki/Binary_Tree#Methods_for_storing_binary_trees.
        /// </para>
        /// <para>
        /// This method is used with the <see cref="BitHelper"/> class. Note that this implementation is
        /// completely different from <see cref="TreeSubSet"/>'s, and that the two should not be mixed.
        /// </para>
        /// </remarks>
        [Rlimit(4)]
        [Requires("@this.SpecNodes.Height <= 30")]
        [Ensures("Result == SpecSearchTree.HeapIndex(@this.SpecComparer, @this.SpecNodes, item, 0)")]
        [Ensures("(Result >= 0) == (Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0)")]
        [Ensures("Result <= SpecSearchTree.Breadth(@this.SpecNodes) - 2")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual int InternalIndexOf(T item)
        {
            Node? current = root;
            int count = 0;
            while (current != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.WellFormed(current) &&
                              SpecSearchTree.IndexRoom(count, Pal.Tree<(T, bool)>(current), Pal.Tree<(T, bool)>(root).Height) &&
                              SpecSearchTree.HeapIndex(comparer, Pal.Tree<(T, bool)>(current), item, count) ==
                              SpecSearchTree.HeapIndex(comparer, Pal.Tree<(T, bool)>(root), item, 0)));
                Pal.Invariant(Pal.Implies(Pal.Returned(),
                              Pal.ReturnValue<int>() == SpecSearchTree.HeapIndex(comparer, Pal.Tree<(T, bool)>(root), item, 0)));
                int order = comparer.Compare(item, current.Item);
                if (order == 0)
                {
                    return count;
                }

                current = order < 0 ? current.Left : current.Right;
                count = order < 0 ? (2 * count + 1) : (2 * count + 2);
            }

            return -1;
        }

        [Ensures("(Result != null) == SpecSearchTree.AnyInRange(@this.SpecComparer, @this.SpecItems, from, to, true, true)")]
        [Ensures("Result == null || Pal.WellFormed(Result) && SpecSearchTree.InRange(@this.SpecComparer, from, to, true, true, SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Result), from))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal Node? FindRange(T? from, T? to) => FindRange(from, to, lowerBoundActive: true, upperBoundActive: true);

        [Ensures("(Result != null) == SpecSearchTree.AnyInRange(@this.SpecComparer, @this.SpecItems, from, to, lowerBoundActive, upperBoundActive)")]
        [Ensures("Result == null || Pal.WellFormed(Result) && SpecSearchTree.InRange(@this.SpecComparer, from, to, lowerBoundActive, upperBoundActive, SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Result), from))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal Node? FindRange(T? from, T? to, bool lowerBoundActive, bool upperBoundActive)
        {
            Node? current = root;
            while (current != null)
            {
                Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.WellFormed(current) &&
                              SpecSearchTree.RangeHit(comparer, Pal.Tree<(T, bool)>(current), from, to, lowerBoundActive, upperBoundActive) ==
                              SpecSearchTree.RangeHit(comparer, Pal.Tree<(T, bool)>(root), from, to, lowerBoundActive, upperBoundActive)));
                Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.ReturnValue<Node?>() != null &&
                              SpecSearchTree.RangeHit(comparer, Pal.Tree<(T, bool)>(root), from, to, lowerBoundActive, upperBoundActive) &&
                              Pal.WellFormed(Pal.ReturnValue<Node?>()) &&
                              SpecSearchTree.InRange(comparer, from, to, lowerBoundActive, upperBoundActive,
                                                     SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(Pal.ReturnValue<Node?>()), from))));
                if (lowerBoundActive && comparer.Compare(from, current.Item) > 0)
                {
                    current = current.Right;
                }
                else
                {
                    if (upperBoundActive && comparer.Compare(to, current.Item) < 0)
                    {
                        current = current.Left;
                    }
                    else
                    {
                        return current;
                    }
                }
            }

            return null;
        }

        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal void UpdateVersion() => ++version;

        /// <summary>
        /// Returns an <see cref="IEqualityComparer{T}"/> object that can be used to create a collection that contains individual sets.
        /// </summary>
        public static IEqualityComparer<SortedSet<T>> CreateSetComparer() => CreateSetComparer(memberEqualityComparer: null);

        /// <summary>
        /// Returns an <see cref="IEqualityComparer{T}"/> object, according to a specified comparer, that can be used to create a collection that contains individual sets.
        /// </summary>
        public static IEqualityComparer<SortedSet<T>> CreateSetComparer(IEqualityComparer<T>? memberEqualityComparer)
        {
            return new SortedSetEqualityComparer<T>(memberEqualityComparer);
        }

        /// <summary>
        /// Decides whether two sets have equal contents, using a fallback comparer if the sets do not have equivalent equality comparers.
        /// </summary>
        /// <param name="set1">The first set.</param>
        /// <param name="set2">The second set.</param>
        /// <param name="comparer">The fallback comparer to use if the sets do not have equal comparers.</param>
        /// <returns><c>true</c> if the sets have equal contents; otherwise, <c>false</c>.</returns>
        internal static bool SortedSetEquals(SortedSet<T>? set1, SortedSet<T>? set2, IComparer<T> comparer)
        {
            if (set1 == null)
            {
                return set2 == null;
            }

            if (set2 == null)
            {
                Debug.Assert(set1 != null);
                return false;
            }

            if (set1.HasEqualComparer(set2))
            {
                return set1.Count == set2.Count && set1.SetEquals(set2);
            }

            bool found;
            foreach (T item1 in set1)
            {
                found = false;
                foreach (T item2 in set2)
                {
                    if (comparer.Compare(item1, item2) == 0)
                    {
                        found = true;
                        break;
                    }
                }
                if (!found)
                {
                    return false;
                }
            }

            return true;
        }

        /// <summary>
        /// Determines whether two <see cref="SortedSet{T}"/> instances have the same comparer.
        /// </summary>
        /// <param name="other">The other <see cref="SortedSet{T}"/>.</param>
        /// <returns>A value indicating whether both sets have the same comparer.</returns>
        private bool HasEqualComparer(SortedSet<T> other)
        {
            // Commonly, both comparers will be the default comparer (and reference-equal). Avoid a virtual method call to Equals() in that case.
            return Comparer == other.Comparer || Comparer.Equals(other.Comparer);
        }

        #endregion

        #region ISet members

        public void UnionWith(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            SortedSet<T>? asSorted = other as SortedSet<T>;
            TreeSubSet? treeSubset = this as TreeSubSet;

            if (treeSubset != null)
                VersionCheck();

            if (asSorted != null && treeSubset == null && Count == 0)
            {
                SortedSet<T> dummy = new SortedSet<T>(asSorted, comparer);
                root = dummy.root;
                count = dummy.count;
                version++;
                return;
            }

            // This actually hurts if N is much greater than M. The / 2 is arbitrary.
            if (asSorted != null && treeSubset == null && HasEqualComparer(asSorted) && (asSorted.Count > this.Count / 2))
            {
                // First do a merge sort to an array.
                T[] merged = new T[asSorted.Count + this.Count];
                int c = 0;
                Enumerator mine = this.GetEnumerator();
                Enumerator theirs = asSorted.GetEnumerator();
                bool mineEnded = !mine.MoveNext(), theirsEnded = !theirs.MoveNext();
                while (!mineEnded && !theirsEnded)
                {
                    int comp = Comparer.Compare(mine.Current, theirs.Current);
                    if (comp < 0)
                    {
                        merged[c++] = mine.Current;
                        mineEnded = !mine.MoveNext();
                    }
                    else if (comp == 0)
                    {
                        merged[c++] = theirs.Current;
                        mineEnded = !mine.MoveNext();
                        theirsEnded = !theirs.MoveNext();
                    }
                    else
                    {
                        merged[c++] = theirs.Current;
                        theirsEnded = !theirs.MoveNext();
                    }
                }

                if (!mineEnded || !theirsEnded)
                {
                    Enumerator remaining = (mineEnded ? theirs : mine);
                    do
                    {
                        merged[c++] = remaining.Current;
                    }
                    while (remaining.MoveNext());
                }

                // now merged has all c elements

                // safe to gc the root, we  have all the elements
                root = null;

                root = ConstructRootFromSortedArray(merged, 0, c - 1, null);
                count = c;
                version++;
            }
            else
            {
                AddAllElements(other);
            }
        }

        [Requires("0 <= startIndex && startIndex <= endIndex + 1 && endIndex < arr.Length")]
        [Requires("arr.Length <= 1073741824")]
        [Requires("Pal.Unshared(redNode) && SpecSearchTree.IsRedLeaf(Pal.Tree<(T, bool)>(redNode))")]
        [Requires("startIndex <= endIndex || redNode == null")]
        [Ensures("Pal.Contents(arr) == Pal.Old(Pal.Contents(arr))")]
        [Ensures("Pal.Unshared(Result) && Pal.Reshaped(redNode, Result)")]
        [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.Build(Pal.Contents(arr), startIndex, endIndex, Pal.Old(Pal.Tree<(T, bool)>(redNode)))")]
        [Ensures("Pal.Implies(redNode == null, SpecSearchTree.IsRedBlack(Pal.Tree<(T, bool)>(Result)) && SpecSearchTree.Keys(Pal.Tree<(T, bool)>(Result)) == Pal.Slice(Pal.Contents(arr), startIndex, endIndex + 1))")]
        [Decreases("endIndex - startIndex + 1")]
        private static Node? ConstructRootFromSortedArray(T[] arr, int startIndex, int endIndex, Node? redNode)
        {
            // You're given a sorted array... say 1 2 3 4 5 6
            // There are 2 cases:
            // -  If there are odd # of elements, pick the middle element (in this case 4), and compute
            //    its left and right branches
            // -  If there are even # of elements, pick the left middle element, save the right middle element
            //    and call the function on the rest
            //    1 2 3 4 5 6 -> pick 3, save 4 and call the fn on 1,2 and 5,6
            //    now add 4 as a red node to the lowest element on the right branch
            //             3                       3
            //         1       5       ->     1        5
            //           2       6             2     4   6
            //    As we're adding to the leftmost of the right branch, nesting will not hurt the red-black properties
            //    Leaf nodes are red if they have no sibling (if there are 2 nodes or if a node trickles
            //    down to the bottom

            // This is done recursively because the iterative way to do this ends up wasting more space than it saves in stack frames
            // Only some base cases are handled below.

            int size = endIndex - startIndex + 1;
            Node root;

            switch (size)
            {
                case 0:
                    return null;
                case 1:
                    root = new Node(arr[startIndex], NodeColor.Black);
                    if (redNode != null)
                    {
                        root.Left = redNode;
                    }
                    break;
                case 2:
                    Pal.Assert(endIndex == startIndex + 1);
                    root = new Node(arr[startIndex], NodeColor.Black);
                    root.Right = new Node(arr[endIndex], NodeColor.Black);
                    Pal.Assert(Pal.Unshared(root));
                    root.Right.ColorRed();
                    if (redNode != null)
                    {
                        root.Left = redNode;
                    }
                    break;
                case 3:
                    Pal.Assert(endIndex == startIndex + 2);
                    root = new Node(arr[startIndex + 1], NodeColor.Black);
                    root.Left = new Node(arr[startIndex], NodeColor.Black);
                    root.Right = new Node(arr[endIndex], NodeColor.Black);
                    Pal.Assert(Pal.Unshared(root));
                    if (redNode != null)
                    {
                        root.Left.Left = redNode;
                        Pal.Assert(Pal.Unshared(root));
                    }
                    break;
                default:
                    int midpt = ((startIndex + endIndex) / 2);
                    Pal.Assert(2 * midpt <= startIndex + endIndex && startIndex + endIndex <= 2 * midpt + 1);
                    Pal.Assert(startIndex + 1 <= midpt && midpt + 1 < endIndex);
                    Pal.Assert(size % 2 != 0 || midpt + 2 <= endIndex);
                    root = new Node(arr[midpt], NodeColor.Black);
                    Pal.Assert(Pal.Unshared(redNode));
                    root.Left = ConstructRootFromSortedArray(arr, startIndex, midpt - 1, redNode);
                    Pal.Assert(Pal.Unshared(root) && Pal.Reshaped(redNode, root));
                    SpecSearchTree.LinkRight<Node, T>(Pal.Old(Pal.Heap<Node>()), Pal.Heap<Node>(), redNode, root);
                    root.Right = size % 2 == 0 ?
                        ConstructRootFromSortedArray(arr, midpt + 2, endIndex, new Node(arr[midpt + 1], NodeColor.Red)) :
                        ConstructRootFromSortedArray(arr, midpt + 1, endIndex, null);
                    Pal.Assert(Pal.Contents(arr) == Pal.Old(Pal.Contents(arr)));
                    SpecSearchTree.BuildSplit<Node, T>(Pal.Old(Pal.Contents(arr)), startIndex, endIndex, midpt, size % 2 == 0, Pal.Old(Pal.Tree<(T, bool)>(redNode)));
                    break;

            }

            return root;
        }

        public virtual void IntersectWith(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (Count == 0)
                return;

            if (other == this)
                return;

            // HashSet<T> optimizations can't be done until equality comparers and comparers are related

            // Technically, this would work as well with an ISorted<T>
            SortedSet<T>? asSorted = other as SortedSet<T>;
            TreeSubSet? treeSubset = this as TreeSubSet;

            if (treeSubset != null)
                VersionCheck();

            if (asSorted != null && treeSubset == null && HasEqualComparer(asSorted))
            {
                // First do a merge sort to an array.
                T[] merged = new T[this.Count];
                int c = 0;
                Enumerator mine = this.GetEnumerator();
                Enumerator theirs = asSorted.GetEnumerator();
                bool mineEnded = !mine.MoveNext(), theirsEnded = !theirs.MoveNext();
                T? max = Max;

                while (!mineEnded && !theirsEnded && Comparer.Compare(theirs.Current, max) <= 0)
                {
                    int comp = Comparer.Compare(mine.Current, theirs.Current);
                    if (comp < 0)
                    {
                        mineEnded = !mine.MoveNext();
                    }
                    else if (comp == 0)
                    {
                        merged[c++] = theirs.Current;
                        mineEnded = !mine.MoveNext();
                        theirsEnded = !theirs.MoveNext();
                    }
                    else
                    {
                        theirsEnded = !theirs.MoveNext();
                    }
                }

                // now merged has all c elements

                // safe to gc the root, we  have all the elements
                root = null;

                root = ConstructRootFromSortedArray(merged, 0, c - 1, null);
                count = c;
                version++;
            }
            else
            {
                IntersectWithEnumerable(other);
            }
        }

        internal virtual void IntersectWithEnumerable(IEnumerable<T> other)
        {
            // TODO: Perhaps a more space-conservative way to do this
            List<T> toSave = new List<T>(Count);
            foreach (T item in other)
            {
                if (Contains(item))
                {
                    toSave.Add(item);
                }
            }

            Clear();
            foreach (T item in toSave)
            {
                Add(item);
            }
        }

        public void ExceptWith(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (Count == 0)
                return;

            if (other == this)
            {
                Clear();
                return;
            }

            SortedSet<T>? asSorted = other as SortedSet<T>;

            if (asSorted != null && HasEqualComparer(asSorted))
            {
                // Outside range, no point in doing anything
                if (comparer.Compare(asSorted.Max, Min) >= 0 && comparer.Compare(asSorted.Min, Max) <= 0)
                {
                    T? min = Min;
                    T? max = Max;
                    foreach (T item in other)
                    {
                        if (comparer.Compare(item, min) < 0)
                            continue;
                        if (comparer.Compare(item, max) > 0)
                            break;
                        Remove(item);
                    }
                }
            }
            else
            {
                RemoveAllElements(other);
            }
        }

        public void SymmetricExceptWith(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (Count == 0)
            {
                UnionWith(other);
                return;
            }

            if (other == this)
            {
                Clear();
                return;
            }

            SortedSet<T>? asSorted = other as SortedSet<T>;

            if (asSorted != null && HasEqualComparer(asSorted))
            {
                SymmetricExceptWithSameComparer(asSorted);
            }
            else
            {
                int length;
                T[] elements = EnumerableHelpers.ToArray(other, out length);
                Array.Sort(elements, 0, length, Comparer);
                SymmetricExceptWithSameComparer(elements, length);
            }
        }

        private void SymmetricExceptWithSameComparer(SortedSet<T> other)
        {
            Debug.Assert(other != null);
            Debug.Assert(HasEqualComparer(other));

            foreach (T item in other)
            {
                bool result = Contains(item) ? Remove(item) : Add(item);
                Debug.Assert(result);
            }
        }

        private void SymmetricExceptWithSameComparer(T[] other, int count)
        {
            Debug.Assert(other != null);
            Debug.Assert(count >= 0 && count <= other.Length);

            if (count == 0)
            {
                return;
            }

            T previous = other[0];
            for (int i = 0; i < count; i++)
            {
                while (i < count && i != 0 && comparer.Compare(other[i], previous) == 0)
                    i++;
                if (i >= count)
                    break;
                T current = other[i];
                bool result = Contains(current) ? Remove(current) : Add(current);
                Debug.Assert(result);
                previous = current;
            }
        }

        public bool IsSubsetOf(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (Count == 0)
            {
                return true;
            }

            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                if (Count > asSorted.Count)
                    return false;
                return IsSubsetOfSortedSetWithSameComparer(asSorted);
            }
            else
            {
                // Worst case: I mark every element in my set and see if I've counted all of them. O(M log N).
                ElementCount result = CheckUniqueAndUnfoundElements(other, false);
                return result.UniqueCount == Count && result.UnfoundCount >= 0;
            }
        }

        private bool IsSubsetOfSortedSetWithSameComparer(SortedSet<T> asSorted)
        {
            SortedSet<T> prunedOther = asSorted.GetViewBetween(Min, Max);
            foreach (T item in this)
            {
                if (!prunedOther.Contains(item))
                    return false;
            }
            return true;
        }

        public bool IsProperSubsetOf(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (other is ICollection c)
            {
                if (Count == 0)
                    return c.Count > 0;
            }

            // another for sorted sets with the same comparer
            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                if (Count >= asSorted.Count)
                    return false;
                return IsSubsetOfSortedSetWithSameComparer(asSorted);
            }

            // Worst case: I mark every element in my set and see if I've counted all of them. O(M log N).
            ElementCount result = CheckUniqueAndUnfoundElements(other, false);
            return result.UniqueCount == Count && result.UnfoundCount > 0;
        }

        public bool IsSupersetOf(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (other is ICollection c && c.Count == 0)
                return true;

            // do it one way for HashSets
            // another for sorted sets with the same comparer
            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                if (Count < asSorted.Count)
                    return false;
                SortedSet<T> pruned = GetViewBetween(asSorted.Min, asSorted.Max);
                foreach (T item in asSorted)
                {
                    if (!pruned.Contains(item))
                        return false;
                }
                return true;
            }

            // and a third for everything else
            return ContainsAllElements(other);
        }

        public bool IsProperSupersetOf(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (Count == 0)
                return false;

            if (other is ICollection c && c.Count == 0)
                return true;

            // another way for sorted sets
            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                if (asSorted.Count >= Count)
                    return false;
                SortedSet<T> pruned = GetViewBetween(asSorted.Min, asSorted.Max);
                foreach (T item in asSorted)
                {
                    if (!pruned.Contains(item))
                        return false;
                }
                return true;
            }

            // Worst case: I mark every element in my set and see if I've counted all of them. O(M log N).
            // slight optimization, put it into a HashSet and then check can do it in O(N+M)
            // but slower in better cases + wastes space
            ElementCount result = CheckUniqueAndUnfoundElements(other, true);
            return result.UniqueCount < Count && result.UnfoundCount == 0;
        }

        public bool SetEquals(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                Enumerator mine = GetEnumerator();
                Enumerator theirs = asSorted.GetEnumerator();
                bool mineEnded = !mine.MoveNext();
                bool theirsEnded = !theirs.MoveNext();
                while (!mineEnded && !theirsEnded)
                {
                    if (Comparer.Compare(mine.Current, theirs.Current) != 0)
                    {
                        return false;
                    }
                    mineEnded = !mine.MoveNext();
                    theirsEnded = !theirs.MoveNext();
                }
                return mineEnded && theirsEnded;
            }

            // Worst case: I mark every element in my set and see if I've counted all of them. O(size of the other collection).
            ElementCount result = CheckUniqueAndUnfoundElements(other, true);
            return result.UniqueCount == Count && result.UnfoundCount == 0;
        }

        public bool Overlaps(IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (Count == 0)
                return false;

            if (other is ICollection<T> c && c.Count == 0)
                return false;

            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted) && (comparer.Compare(Min, asSorted.Max) > 0 || comparer.Compare(Max, asSorted.Min) < 0))
            {
                return false;
            }

            foreach (T item in other)
            {
                if (Contains(item))
                {
                    return true;
                }
            }

            return false;
        }

        /// <summary>
        /// This works similar to HashSet's CheckUniqueAndUnfound (description below), except that the bit
        /// array maps differently than in the HashSet. We can only use this for the bulk boolean checks.
        ///
        /// Determines counts that can be used to determine equality, subset, and superset. This
        /// is only used when other is an IEnumerable and not a HashSet. If other is a HashSet
        /// these properties can be checked faster without use of marking because we can assume
        /// other has no duplicates.
        ///
        /// The following count checks are performed by callers:
        /// 1. Equals: checks if UnfoundCount = 0 and uniqueFoundCount = Count; i.e. everything
        /// in other is in this and everything in this is in other
        /// 2. Subset: checks if UnfoundCount >= 0 and uniqueFoundCount = Count; i.e. other may
        /// have elements not in this and everything in this is in other
        /// 3. Proper subset: checks if UnfoundCount > 0 and uniqueFoundCount = Count; i.e
        /// other must have at least one element not in this and everything in this is in other
        /// 4. Proper superset: checks if unfound count = 0 and uniqueFoundCount strictly less
        /// than Count; i.e. everything in other was in this and this had at least one element
        /// not contained in other.
        ///
        /// An earlier implementation used delegates to perform these checks rather than returning
        /// an ElementCount struct; however this was changed due to the perf overhead of delegates.
        /// </summary>
        private unsafe ElementCount CheckUniqueAndUnfoundElements(IEnumerable<T> other, bool returnIfUnfound)
        {
            ElementCount result;

            // need special case in case this has no elements.
            if (Count == 0)
            {
                int numElementsInOther = 0;
                foreach (T item in other)
                {
                    numElementsInOther++;
                    // break right away, all we want to know is whether other has 0 or 1 elements
                    break;
                }
                result.UniqueCount = 0;
                result.UnfoundCount = numElementsInOther;
                return result;
            }

            int originalLastIndex = Count;
            int intArrayLength = BitHelper.ToIntArrayLength(originalLastIndex);

            Span<int> span = stackalloc int[StackAllocThreshold];
            BitHelper bitHelper = (uint)intArrayLength <= StackAllocThreshold ?
                new BitHelper(span.Slice(0, intArrayLength), clear: true) :
                new BitHelper(new int[intArrayLength], clear: false);

            // count of items in other not found in this
            int UnfoundCount = 0;
            // count of unique items in other found in this
            int uniqueFoundCount = 0;

            foreach (T item in other)
            {
                int index = InternalIndexOf(item);
                if (index >= 0)
                {
                    if (!bitHelper.IsMarked(index))
                    {
                        // item hasn't been seen yet
                        bitHelper.MarkBit(index);
                        uniqueFoundCount++;
                    }
                }
                else
                {
                    UnfoundCount++;
                    if (returnIfUnfound)
                    {
                        break;
                    }
                }
            }

            result.UniqueCount = uniqueFoundCount;
            result.UnfoundCount = UnfoundCount;
            return result;
        }

        // pal: R27.40. The breadth-first walk collects the members `match` holds of; each is
        // then removed, so what is left is exactly the members it rejects, in order. `match`
        // is not null (R10), so `ThrowIfNull` is nothing, as it is for CopyTo's `array`.
        [Ensures("@this.SpecItems == Pal.RemoveAll(Pal.Old(@this.SpecItems), match)")]
        [Ensures("Result == Pal.Old(@this.SpecItems).Length - @this.SpecItems.Length")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Rlimit(20)]
        public int RemoveWhere(Predicate<T> match)
        {
            ArgumentNullException.ThrowIfNull(match);

            List<T> matches = new List<T>(this.Count);
            Ghost<Seq<T>> s0 = this.SpecItems;

            BreadthFirstTreeWalk(n =>
            {
                Pal.Protocol<(T, bool), bool>(tr => SpecWalk.Collected(tr, matches.Items, match));
                if (match(n.Item))
                {
                    matches.Add(n.Item);
                }
                return true;
            });

            Ghost<Seq<T>> m0 = matches.Items;
            SpecSetFilter.RemovingStart(this.SpecComparer, s0.Value, m0.Value);

            // Enumerate the results of the breadth-first walk in reverse in an attempt to lower cost.
            int actuallyRemoved = 0;
            for (int i = matches.Count - 1; i >= 0; i--)
            {
                Pal.Invariant(-1 <= i && i < m0.Value.Length);
                Pal.Invariant(matches.Items == m0.Value && this.SpecComparer == Pal.Old(this.SpecComparer));
                Pal.Invariant(SpecSetFilter.Removing(this.SpecComparer, s0.Value, this.SpecItems, m0.Value, i));
                Pal.Invariant(actuallyRemoved == s0.Value.Length - this.SpecItems.Length);
                Pal.Invariant(Pal.Forall((T y) => Pal.Implies(SpecSetFilter.Contains(m0.Value, y), SpecSetFilter.Contains(s0.Value, y) && match(y)) &&
                                                  Pal.Implies(SpecSetFilter.Contains(s0.Value, y) && match(y), SpecSetFilter.Contains(m0.Value, y))));
                Pal.Decreases(i + 1);
                SpecSetFilter.RemovingStep(this.SpecComparer, s0.Value, this.SpecItems, m0.Value, i);
                if (Remove(matches[i]))
                {
                    actuallyRemoved++;
                }
            }

            SpecSetFilter.FilterUnique(this.SpecComparer, s0.Value, this.SpecItems, match);
            return actuallyRemoved;
        }

        #endregion

        #region ISorted members

        [Ensures("Pal.Same(Result, @this.SpecItems.Length > 0 ? @this.SpecItems[0] : default(T))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public T? Min => MinInternal;

        [Ensures("Pal.Same(Result, @this.SpecItems.Length > 0 ? @this.SpecItems[0] : default(T))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual T? MinInternal
        {
            get
            {
                if (root == null)
                {
                    return default;
                }

                Node current = root;
                while (current.Left != null)
                {
                    Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                    Pal.Invariant(Pal.WellFormed(current) && current != null);
                    Pal.Invariant(Pal.Forall((T d) => Pal.Same(SpecSearchTree.Leftmost(Pal.Tree<(T, bool)>(current), d),
                                                               SpecSearchTree.Leftmost(Pal.Tree<(T, bool)>(root), d))));
                    current = current.Left;
                }

                return current.Item;
            }
        }

        [Ensures("Pal.Same(Result, @this.SpecItems.Length > 0 ? @this.SpecItems[@this.SpecItems.Length - 1] : default(T))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public T? Max => MaxInternal;

        [Ensures("Pal.Same(Result, @this.SpecItems.Length > 0 ? @this.SpecItems[@this.SpecItems.Length - 1] : default(T))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal virtual T? MaxInternal
        {
            get
            {
                if (root == null)
                {
                    return default;
                }

                Node current = root;
                while (current.Right != null)
                {
                    Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                    Pal.Invariant(Pal.WellFormed(current) && current != null);
                    Pal.Invariant(Pal.Forall((T d) => Pal.Same(SpecSearchTree.Rightmost(Pal.Tree<(T, bool)>(current), d),
                                                               SpecSearchTree.Rightmost(Pal.Tree<(T, bool)>(root), d))));
                    current = current.Right;
                }

                return current.Item;
            }
        }

        public IEnumerable<T> Reverse()
        {
            Enumerator e = new Enumerator(this, reverse: true);
            while (e.MoveNext())
            {
                yield return e.Current;
            }
        }

        public virtual SortedSet<T> GetViewBetween(T? lowerValue, T? upperValue)
        {
            if (Comparer.Compare(lowerValue, upperValue) > 0)
            {
                throw new ArgumentException(SR.SortedSet_LowerValueGreaterThanUpperValue, nameof(lowerValue));
            }
            return new TreeSubSet(this, lowerValue, upperValue, true, true);
        }

#if DEBUG
        /// <summary>
        /// debug status to be checked whenever any operation is called
        /// </summary>
        /// <returns></returns>
        internal virtual bool versionUpToDate()
        {
            return true;
        }
#endif

        void ISerializable.GetObjectData(SerializationInfo info, StreamingContext context) => GetObjectData(info, context);

        protected virtual void GetObjectData(SerializationInfo info, StreamingContext context)
        {
            ArgumentNullException.ThrowIfNull(info);

            info.AddValue(CountName, count); // This is the length of the bucket array.
            info.AddValue(ComparerName, comparer, typeof(IComparer<T>));
            info.AddValue(VersionName, version);

            if (root != null)
            {
                T[] items = new T[Count];
                CopyTo(items, 0);
                info.AddValue(ItemsName, items, typeof(T[]));
            }
        }

        void IDeserializationCallback.OnDeserialization(object? sender) => OnDeserialization(sender);

        protected virtual void OnDeserialization(object? sender)
        {
            if (comparer != null)
            {
                return; // Somebody had a dependency on this class and fixed us up before the ObjectManager got to it.
            }

            if (siInfo == null)
            {
                throw new SerializationException(SR.Serialization_InvalidOnDeser);
            }

            comparer = (IComparer<T>)siInfo.GetValue(ComparerName, typeof(IComparer<T>))!;
            int savedCount = siInfo.GetInt32(CountName);

            if (savedCount != 0)
            {
                T[]? items = (T[]?)siInfo.GetValue(ItemsName, typeof(T[]));

                if (items == null)
                {
                    throw new SerializationException(SR.Serialization_MissingValues);
                }

                for (int i = 0; i < items.Length; i++)
                {
                    Add(items[i]);
                }
            }

            version = siInfo.GetInt32(VersionName);
            if (count != savedCount)
            {
                throw new SerializationException(SR.Serialization_MismatchedCount);
            }

            siInfo = null;
        }

        #endregion

        #region Helper classes

        [Region]
        internal sealed class Node
        {
            public Node(T item, NodeColor color)
            {
                Item = item;
                Color = color;
            }

            [Requires("node == null || Pal.InRegion(node)")]
            [Ensures("Result == (node != null && Pal.InRegion(node) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(node)))")]
            public static bool IsNonNullBlack(Node? node) => node != null && node.IsBlack;

            [Requires("node == null || Pal.InRegion(node)")]
            [Ensures("Result == (node != null && Pal.InRegion(node) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(node)))")]
            public static bool IsNonNullRed(Node? node) => node != null && node.IsRed;

            [Requires("node == null || Pal.InRegion(node)")]
            [Ensures("Result == (node == null || !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(node)))")]
            public static bool IsNullOrBlack(Node? node) => node == null || node.IsBlack;

            public T Item { get; set; }

            public Node? Left { get; set; }

            public Node? Right { get; set; }

            public NodeColor Color { get; set; }

            [Model]
            private (T, bool) View => (Item, Color == NodeColor.Red);

            [Requires("Pal.InRegion(@this)")]
            [Ensures("Result == !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this))")]
            public bool IsBlack => Color == NodeColor.Black;

            [Requires("Pal.InRegion(@this)")]
            [Ensures("Result == SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this))")]
            public bool IsRed => Color == NodeColor.Red;

            [Requires("Pal.WellFormed(@this)")]
            [Ensures("Result == (!SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this)) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right))")]
            public bool Is2Node => IsBlack && IsNullOrBlack(Left) && IsNullOrBlack(Right);

            [Requires("Pal.WellFormed(@this)")]
            [Ensures("Result == (SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right))")]
            public bool Is4Node => IsNonNullRed(Left) && IsNonNullRed(Right);

            [Requires("Pal.Unshared(@this)")]
            [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
            [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Recolor(Pal.Old(Pal.Tree<(T, bool)>(@this)), false)")]
            [Ensures("SpecTopDown.Recolored<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this, false)")]
            public void ColorBlack() => Color = NodeColor.Black;

            [Requires("Pal.Unshared(@this)")]
            [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
            [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Recolor(Pal.Old(Pal.Tree<(T, bool)>(@this)), true)")]
            [Ensures("SpecTopDown.Recolored<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this, true)")]
            public void ColorRed() => Color = NodeColor.Red;

            public Node DeepClone(int count)
            {
#if DEBUG
                Debug.Assert(count == GetCount());
#endif
                Node newRoot = ShallowClone();

                var pendingNodes = new Stack<(Node source, Node target)>(2 * Log2(count) + 2);
                pendingNodes.Push((this, newRoot));

                while (pendingNodes.TryPop(out var next))
                {
                    Node clonedNode;

                    if (next.source.Left is Node left)
                    {
                        clonedNode = left.ShallowClone();
                        next.target.Left = clonedNode;
                        pendingNodes.Push((left, clonedNode));
                    }

                    if (next.source.Right is Node right)
                    {
                        clonedNode = right.ShallowClone();
                        next.target.Right = clonedNode;
                        pendingNodes.Push((right, clonedNode));
                    }
                }

                return newRoot;
            }

            /// <summary>
            /// Gets the rotation this node should undergo during a removal.
            /// </summary>
            [Requires("Pal.Unshared(@this) && Pal.InRegion(sibling)")]
            [Requires("current == Pal.LeftOf(@this) && sibling == Pal.RightOf(@this) || current == Pal.RightOf(@this) && sibling == Pal.LeftOf(@this)")]
            [Requires("SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(sibling).Left) || SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(sibling).Right)")]
            [Ensures("Pal.Implies(current == Pal.LeftOf(@this), Result == (SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(sibling).Left) ? TreeRotation.RightLeft : TreeRotation.Left))")]
            [Ensures("Pal.Implies(current != Pal.LeftOf(@this), Result == (SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(sibling).Left) ? TreeRotation.Right : TreeRotation.LeftRight))")]
            [Ensures("SpecSearchTree.CanRotate(Result, Pal.Tree<(T, bool)>(@this))")]
            public TreeRotation GetRotation(Node current, Node sibling)
            {
                Debug.Assert(IsNonNullRed(sibling.Left) || IsNonNullRed(sibling.Right));
#if DEBUG
                Debug.Assert(HasChildren(current, sibling));
#endif

                bool currentIsLeftChild = Left == current;
                return IsNonNullRed(sibling.Left) ?
                    (currentIsLeftChild ? TreeRotation.RightLeft : TreeRotation.Right) :
                    (currentIsLeftChild ? TreeRotation.Left : TreeRotation.LeftRight);
            }

            /// <summary>
            /// Gets the sibling of one of this node's children.
            /// </summary>
            [Requires("Pal.Unshared(@this)")]
            [Requires("node == Pal.LeftOf(@this) && Pal.RightOf(@this) != null || node == Pal.RightOf(@this) && Pal.LeftOf(@this) != null")]
            [Requires("Pal.LeftOf(@this) != Pal.RightOf(@this)")]
            [Ensures("Pal.Implies(node == Pal.LeftOf(@this), Result == Pal.RightOf(@this))")]
            [Ensures("Pal.Implies(node != Pal.LeftOf(@this), Result == Pal.LeftOf(@this))")]
            public Node GetSibling(Node node)
            {
                Debug.Assert(node != null);
                Debug.Assert(node == Left ^ node == Right);

                return node == Left ? Right! : Left!;
            }

            [Requires("Pal.InRegion(@this)")]
            [Ensures("Pal.Unshared(Result) && Pal.Reshaped(null, Result)")]
            [Ensures("Pal.Tree<(T, bool)>(Result) == Pal.Old(Pal.Tree<(T, bool)>(@this)).RootOnly")]
            public Node ShallowClone() => new Node(Item, Color);

            [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf")]
            [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
            [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Split4(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
            [Ensures("SpecTopDown.Split4ed<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this)")]
            public void Split4Node()
            {
                Debug.Assert(Left != null);
                Debug.Assert(Right != null);

                ColorRed();
                Left.ColorBlack();
                Right.ColorBlack();
            }

            /// <summary>
            /// Does a rotation on this tree. May change the color of a grandchild from red to black.
            /// </summary>
            [Requires("Pal.Unshared(@this) && SpecSearchTree.CanRotate(rotation, Pal.Tree<(T, bool)>(@this))")]
            [Ensures("Result != null && Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
            [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.Rotate(rotation, Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
            [Ensures("SpecTopDownRemove.RotatedN<SortedSet<T>.Node, T, TreeRotation>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this, Result, rotation)")]
            public Node? Rotate(TreeRotation rotation)
            {
                Ghost<SpecHeap<Node>> h0 = Pal.Heap<Node>();
                Node removeRed;
                switch (rotation)
                {
                    case TreeRotation.Right:
                        removeRed = Left!.Left!;
                        Debug.Assert(removeRed.IsRed);
                        removeRed.ColorBlack();
                        SpecTopDownRemove.RotSingle<Node, T>(h0.Value, Pal.Heap<Node>(), this, removeRed, false);
                        return RotateRight();
                    case TreeRotation.Left:
                        removeRed = Right!.Right!;
                        Debug.Assert(removeRed.IsRed);
                        removeRed.ColorBlack();
                        SpecTopDownRemove.RotSingle<Node, T>(h0.Value, Pal.Heap<Node>(), this, removeRed, true);
                        return RotateLeft();
                    case TreeRotation.RightLeft:
                        Debug.Assert(Right!.Left!.IsRed);
                        SpecTopDownRemove.RotDouble<Node, T>(h0.Value, this, false);
                        return RotateRightLeft();
                    case TreeRotation.LeftRight:
                        Debug.Assert(Left!.Right!.IsRed);
                        SpecTopDownRemove.RotDouble<Node, T>(h0.Value, this, true);
                        return RotateLeftRight();
                    default:
                        Debug.Fail($"{nameof(rotation)}: {rotation} is not a defined {nameof(TreeRotation)} value.");
                        return null;
                }
            }

            /// <summary>
            /// Does a left rotation on this tree, making this node the new left child of the current right child.
            /// </summary>
            [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf")]
            [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
            [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateLeft(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
            [Ensures("SpecTopDown.Rotated<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this, Result, true, true)")]
            [Ensures("Result == Pal.Old(Pal.RightOf(@this))")]
            public Node RotateLeft()
            {
                Node child = Right!;
                Right = child.Left;
                child.Left = this;
                return child;
            }

            /// <summary>
            /// Does a left-right rotation on this tree. The left child is rotated left, then this node is rotated right.
            /// </summary>
            [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !Pal.Tree<(T, bool)>(@this).Left.Right.IsLeaf")]
            [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
            [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateLeftRight(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
            [Ensures("SpecTopDown.Rotated<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this, Result, true, false)")]
            [Rlimit(200)]
            public Node RotateLeftRight()
            {
                Node child = Left!;
                Node grandChild = child.Right!;

                Left = grandChild.Right;
                grandChild.Right = this;
                child.Right = grandChild.Left;
                grandChild.Left = child;
                return grandChild;
            }

            /// <summary>
            /// Does a right rotation on this tree, making this node the new right child of the current left child.
            /// </summary>
            [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Left.IsLeaf")]
            [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
            [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateRight(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
            [Ensures("SpecTopDown.Rotated<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this, Result, false, false)")]
            [Ensures("Result == Pal.Old(Pal.LeftOf(@this))")]
            public Node RotateRight()
            {
                Node child = Left!;
                Left = child.Right;
                child.Right = this;
                return child;
            }

            /// <summary>
            /// Does a right-left rotation on this tree. The right child is rotated right, then this node is rotated left.
            /// </summary>
            [Requires("Pal.Unshared(@this) && !Pal.Tree<(T, bool)>(@this).Right.IsLeaf && !Pal.Tree<(T, bool)>(@this).Right.Left.IsLeaf")]
            [Ensures("Pal.Unshared(Result) && Pal.Reshaped(@this, Result)")]
            [Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.RotateRightLeft(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
            [Ensures("SpecTopDown.Rotated<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this, Result, false, true)")]
            [Rlimit(200)]
            public Node RotateRightLeft()
            {
                Node child = Right!;
                Node grandChild = child.Left!;

                Right = grandChild.Left;
                grandChild.Left = this;
                child.Left = grandChild.Right;
                grandChild.Right = child;
                return grandChild;
            }

            /// <summary>
            /// Combines two 2-nodes into a 4-node.
            /// </summary>
            [Requires("Pal.Unshared(@this) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this))")]
            [Requires("!Pal.Tree<(T, bool)>(@this).Left.IsLeaf && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left.Left) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Left.Right)")]
            [Requires("!Pal.Tree<(T, bool)>(@this).Right.IsLeaf && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right.Left) && !SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(@this).Right.Right)")]
            [Ensures("Pal.Unshared(@this) && Pal.Reshaped(@this, @this)")]
            [Ensures("Pal.Tree<(T, bool)>(@this) == SpecSearchTree.Merge2(Pal.Old(Pal.Tree<(T, bool)>(@this)))")]
            [Ensures("SpecTopDownRemove.Merged<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this)")]
            public void Merge2Nodes()
            {
                Debug.Assert(IsRed);
                Debug.Assert(Left!.Is2Node);
                Debug.Assert(Right!.Is2Node);

                // Combine two 2-nodes into a 4-node.
                ColorBlack();
                Left.ColorRed();
                Right.ColorRed();
            }

            /// <summary>
            /// Replaces a child of this node with a new node.
            /// </summary>
            /// <param name="child">The child to replace.</param>
            /// <param name="newChild">The node to replace <paramref name="child"/> with.</param>
            [Requires("Pal.InRegion(@this)")]
            [Ensures("SpecTopDown.Relinked<SortedSet<T>.Node, T>(Pal.Old(Pal.Heap<SortedSet<T>.Node>()), Pal.Heap<SortedSet<T>.Node>(), @this, child, newChild)")]
            public void ReplaceChild(Node child, [System.Diagnostics.CodeAnalysis.AllowNull] Node newChild)
            {
#if DEBUG
                Debug.Assert(HasChild(child));
#endif

                if (Left == child)
                {
                    Left = newChild;
                }
                else
                {
                    Right = newChild;
                }
            }

#if DEBUG
            private int GetCount() => 1 + (Left?.GetCount() ?? 0) + (Right?.GetCount() ?? 0);

            private bool HasChild(Node child) => child == Left || child == Right;

            private bool HasChildren(Node child1, Node child2)
            {
                Debug.Assert(child1 != child2);

                return (Left == child1 && Right == child2)
                    || (Left == child2 && Right == child1);
            }
#endif
        }

        public struct Enumerator : IEnumerator<T>, IEnumerator, ISerializable, IDeserializationCallback
        {
            private readonly SortedSet<T> _tree;
            private readonly int _version;

            private readonly Stack<Node> _stack;
            private Node? _current;

            private readonly bool _reverse;

            [Ensures("ReferenceEquals(@this._tree, set) && @this._version == set.SpecVersion && !@this._reverse")]
            [Ensures("SpecWalk.Walkable<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)")]
            [Ensures("SpecWalk.Pending<SortedSet<T>.Node, T>(false, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items) == set.SpecItems")]
            internal Enumerator(SortedSet<T> set)
                : this(set, reverse: false)
            {
            }

            [Ensures("ReferenceEquals(@this._tree, set) && @this._version == set.SpecVersion && @this._reverse == reverse")]
            [Ensures("SpecWalk.Walkable<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)")]
            [Ensures("SpecWalk.Pending<SortedSet<T>.Node, T>(reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items) == (reverse ? Pal.Reverse(set.SpecItems) : set.SpecItems)")]
            [Wrapping]
            internal Enumerator(SortedSet<T> set, bool reverse)
            {
                _tree = set;
                set.VersionCheck();
                _version = set.version;

                // 2 log(n + 1) is the maximum height.
                _stack = new Stack<Node>(2 * (int)Log2(set.TotalCount() + 1));
                _current = null;
                _reverse = reverse;

                Initialize();
            }

            void ISerializable.GetObjectData(SerializationInfo info, StreamingContext context)
            {
                throw new PlatformNotSupportedException();
            }

            void IDeserializationCallback.OnDeserialization(object? sender)
            {
                throw new PlatformNotSupportedException();
            }

            [Rlimit(40)]
            [Requires("@this._stack.SpecCount == 0")]
            [Ensures("SpecWalk.Walkable<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)")]
            [Ensures("SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items) == SpecWalk.Keys(@this._reverse, @this._tree.SpecNodes)")]
            private void Initialize()
            {
                _current = null;
                Node? node = _tree.root;
                Node? next, other;
                SpecWalk.Empty<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items);
                while (node != null)
                {
                    Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                    Pal.Invariant(Pal.WellFormed(node) && SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), _stack.Items) &&
                                  SpecSearchTree.Keys(Pal.Tree<(T, bool)>(_tree.root)).Length == _tree.count &&
                                  Pal.Concat(SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(node)),
                                             SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items)) ==
                                  SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(_tree.root)));
                    SpecWalk.Length<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items);
                    SpecWalk.Descend<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items, node);
                    Pal.Assert(Pal.Tree<(T, bool)>(_tree.root).Size == _tree.count);
                    Pal.Assert(_stack.Items.Length < _tree.count);
                    next = (_reverse ? node.Right : node.Left);
                    other = (_reverse ? node.Left : node.Right);
                    if (_tree.IsWithinRange(node.Item))
                    {
                        _stack.Push(node);
                        node = next;
                    }
                    else if (next == null || !_tree.IsWithinRange(next.Item))
                    {
                        node = other;
                    }
                    else
                    {
                        node = next;
                    }
                }
                Pal.Assert(Pal.Concat(SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(node)),
                                      SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items)) ==
                           SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items));
            }

            [Requires("SpecWalk.Walkable<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)")]
            [Requires("SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items).Length <= @this._tree.SpecCount")]
            [Rlimit(40)]
            [Throws(typeof(InvalidOperationException), "@this._version != @this._tree.SpecVersion")]
            [Ensures("SpecWalk.Walkable<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)")]
            [Ensures("Result == (Pal.Old(SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)).Length > 0)")]
            [Ensures("Pal.Implies(!Result, @this._current == null)")]
            [Ensures("Pal.Implies(Result, @this._current != null && Pal.WellFormed(@this._current) && " +
                     "Pal.Same(SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(@this._current), Pal.Old(SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items))[0]), Pal.Old(SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items))[0]))")]
            [Ensures("SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items) == Pal.Slice(Pal.Old(SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)), Result ? 1 : 0, Pal.Old(SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)).Length)")]
            public bool MoveNext()
            {
                // Make sure that the underlying subset has not been changed since
                _tree.VersionCheck();

                if (_version != _tree.version)
                {
                    throw new InvalidOperationException(SR.InvalidOperation_EnumFailedVersion);
                }

                if (_stack.Count == 0)
                {
                    _current = null;
                    return false;
                }

                Ghost<Seq<T>> p0 = SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items);
                Pal.Assert(SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items) == Pal.Slice(p0.Value, 0, p0.Value.Length));
                SpecWalk.PopAt<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items, p0.Value, 0);
                _current = _stack.Pop();
                Node? node = (_reverse ? _current.Left : _current.Right);
                Node? next, other;
                while (node != null)
                {
                    Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                    Pal.Invariant(Pal.WellFormed(node) && SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), _stack.Items) &&
                                  p0.Value.Length <= _tree.count &&
                                  Pal.Concat(SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(node)),
                                             SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items)) ==
                                  Pal.Slice(p0.Value, 1, p0.Value.Length));
                    SpecWalk.Length<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items);
                    SpecWalk.Descend<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items, node);
                    Pal.Assert(_stack.Items.Length < p0.Value.Length);
                    next = (_reverse ? node.Right : node.Left);
                    other = (_reverse ? node.Left : node.Right);
                    if (_tree.IsWithinRange(node.Item))
                    {
                        _stack.Push(node);
                        node = next;
                    }
                    else if (other == null || !_tree.IsWithinRange(other.Item))
                    {
                        node = next;
                    }
                    else
                    {
                        node = other;
                    }
                }
                Pal.Assert(Pal.Concat(SpecWalk.Keys(_reverse, Pal.Tree<(T, bool)>(node)),
                                      SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items)) ==
                           SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items));
                return true;
            }

            [Ensures("true")]
            public void Dispose() { }

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
                    return default(T)!; // Should only happen when accessing Current is undefined behavior
                }
            }

            [Requires("@this._current == null || Pal.InRegion(@this._current)")]
            [Throws(typeof(InvalidOperationException), "@this._current == null")]
            [Ensures("@this._current != null && Pal.Exists((T v) => Pal.Boxes(Result, v) && Pal.Same(v, SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(@this._current), v)))")]
            object? IEnumerator.Current
            {
                get
                {
                    if (_current == null)
                    {
                        throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                    }

                    return _current.Item;
                }
            }

            [Ensures("Result == (@this._current == null)")]
            internal bool NotStartedOrEnded => _current == null;

            [Throws(typeof(InvalidOperationException), "@this._version != @this._tree.SpecVersion")]
            [Ensures("SpecWalk.Walkable<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)")]
            [Ensures("SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items) == SpecWalk.Keys(@this._reverse, @this._tree.SpecNodes)")]
            internal void Reset()
            {
                if (_version != _tree.version)
                {
                    throw new InvalidOperationException(SR.InvalidOperation_EnumFailedVersion);
                }

                _stack.Clear();
                Initialize();
            }

            [Throws(typeof(InvalidOperationException), "@this._version != @this._tree.SpecVersion")]
            [Ensures("SpecWalk.Walkable<SortedSet<T>.Node, T>(Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items)")]
            [Ensures("SpecWalk.Pending<SortedSet<T>.Node, T>(@this._reverse, Pal.Heap<SortedSet<T>.Node>(), @this._stack.Items) == SpecWalk.Keys(@this._reverse, @this._tree.SpecNodes)")]
            void IEnumerator.Reset() => Reset();
        }

        internal struct ElementCount
        {
            internal int UniqueCount;
            internal int UnfoundCount;
        }

        #endregion

        #region Miscellaneous

        /// <summary>
        /// Searches the set for a given value and returns the equal value it finds, if any.
        /// </summary>
        /// <param name="equalValue">The value to search for.</param>
        /// <param name="actualValue">The value from the set that the search found, or the default value of <typeparamref name="T"/> when the search yielded no match.</param>
        /// <returns>A value indicating whether the search was successful.</returns>
        /// <remarks>
        /// This can be useful when you want to reuse a previously stored reference instead of
        /// a newly constructed one (so that more sharing of references can occur) or to look up
        /// a value that has more complete data than the value you currently have, although their
        /// comparer functions indicate they are equal.
        /// </remarks>
        [Ensures("Result == (Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, equalValue) >= 0)")]
        [Ensures("Pal.Implies(Result, Pal.Same(actualValue, @this.SpecItems[Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, equalValue)]))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public bool TryGetValue(T equalValue, [MaybeNullWhen(false)] out T actualValue)
        {
            Node? node = FindNode(equalValue);
            if (node != null)
            {
                actualValue = node.Item;
                return true;
            }
            actualValue = default;
            return false;
        }

        // Used for set checking operations (using enumerables) that rely on counting
        [Wrapping]
        [Ensures("0 <= Result && Result <= 31")]
        private static int Log2(int value) => BitOperations.Log2((uint)value);

        #endregion
    }
}
