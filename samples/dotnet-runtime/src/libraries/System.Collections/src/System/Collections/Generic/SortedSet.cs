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
        /// <summary>R32.10. The root pointer: names the tree's nodes in the set's region.</summary>
#pragma warning disable CS0649 // Specification model field, initialized only in PAL builds.
        internal SortedSet<T>.Node? Root;
#pragma warning restore CS0649
#if PAL
        internal SortedSetLabels<T> Labels;
        internal SortedSetObservation<T> Observation;
#endif
    }

    [DebuggerTypeProxy(typeof(ICollectionDebugView<>))]
    [DebuggerDisplay("Count = {Count}")]
    [Serializable]
    [System.Runtime.CompilerServices.TypeForwardedFrom("System, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    [Invariant("SortedSetOwnership.Owner(root, ownershipState, Pal.Permission())")]
    public partial class SortedSet<T> : ISet<T>, ICollection<T>, ICollection, IReadOnlyCollection<T>, IReadOnlySet<T>, ISerializable, IDeserializationCallback
    {
        #region Local variables/constants

        private Node? root;
        private IComparer<T> comparer = default!;
        private int count;
        [Wrapping] private int version;
#if PAL
        private SortedSetOwnershipState<T> ownershipState = SortedSetOwnership.Empty<T>();
#endif

#if PAL
        [Refine("Pal.StrictlySorted(Result.Comparer, SpecSearchTree.Keys(Result.Tree))")]
        [Refine("SpecSearchTree.IsRedBlack(Result.Tree)")]
        [Refine("Result.Count == Result.Tree.Size")]
        [Refine("Result.Count <= int.MaxValue")]
        [Refine("Result.Comparer != null")]
        [Refine("SortedSetOwnership.Good(Result.Labels)")]
        [Refine("Result.Root == SortedSetOwnership.Top(Result.Labels)")]
        [Refine("Result.Tree == SortedSetOwnership.Values(Result.Labels)")]
        [Model]
        private SortedSetModel<T> Model => new SortedSetModel<T>
        {
            Tree = SortedSetOwnership.Values(SortedSetOwnership.Active(ownershipState)),
            Comparer = comparer,
            Count = count,
            Version = version,
            Root = root,
            Labels = SortedSetOwnership.Active(ownershipState),
            Observation = SortedSetState.Observe(ownershipState),
        };
#else
        [Model]
        private SortedSetModel<T> Model => throw new InvalidOperationException("Specification only");
#endif

        [Spec]
        public SpecInt SpecCount => Model.Count;

        /// <summary>R32.10. The root pointer, in the set's region.</summary>
        [Spec]
        internal Node? SpecRoot => Model.Root;
#if PAL
        [Spec]
        internal SortedSetLabels<T> SpecLabels => Model.Labels;
        [Spec]
        internal SortedSetObservation<T> SpecObservation => Model.Observation;
        [Spec]
        internal SortedSetModel<T> SpecSnapshot => Model;
#endif

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

        // pal: §37. The range `CheckUniqueAndUnfoundElements` counts over, and the tree whose
        // range root it searches. A set's range has no bound, and its tree is its own; a view
        // overrides each, and its replica of the method reads the overrides (R37.7). A bound
        // is a sequence: a set has no key to name one by.
        [Spec] internal virtual Seq<T> SpecRangeLo => SortedSetCount.None<T>();
        [Spec] internal virtual Seq<T> SpecRangeHi => SortedSetCount.None<T>();
        [Spec] internal virtual bool SpecRangeLa => false;
        [Spec] internal virtual bool SpecRangeUa => false;
        [Spec] internal virtual SpecTree<(T, bool)> SpecRangeTree => Model.Tree;
        [Spec] internal virtual IComparer<T> SpecRangeComparer => Model.Comparer;
        [Spec] internal virtual bool SpecRangeReady => true;

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
#if PAL
            SortedSetOwnershipProof.Empty<T>();
#endif
            comparer = Comparer<T>.Default;
        }

        [Ensures("@this.SpecItems.Length == 0")]
        [Ensures("@this.SpecComparer == (comparer == null ? Comparer<T>.Default : comparer)")]
        public SortedSet(IComparer<T>? comparer)
        {
#if PAL
            SortedSetOwnershipProof.Empty<T>();
#endif
            this.comparer = comparer ?? Comparer<T>.Default;
        }


        [Requires("Comparer<T>.Default == collection.SpecComparer || !SpecSortDedupe.ComparerEquals(Comparer<T>.Default, collection.SpecComparer)")]
        [Requires("Pal.Implies(Comparer<T>.Default != collection.SpecComparer, 2 * collection.SpecItems.Length + 2 <= 1073741824)")]
        [Ensures("@this.SpecComparer == Comparer<T>.Default")]
        [Ensures("SpecSortDedupe.SetOf(@this.SpecComparer, @this.SpecItems, collection.SpecItems)")]
        [Ensures("Pal.Implies(@this.SpecComparer == collection.SpecComparer, @this.SpecItems == collection.SpecItems)")]
        [Ensures("collection.SpecItems == Pal.Old(collection.SpecItems)")]
        [Ensures("collection.SpecComparer == Pal.Old(collection.SpecComparer)")]
        public SortedSet([Exactly(typeof(SortedSet<>))] IEnumerable<T> collection) : this(collection, Comparer<T>.Default) { }

        // A set whose comparer is not this one's but `Equals` it is copied as it stands, its
        // tree in the other comparer's order: the contract excludes that case (R27.47,
        // R34.27). With another comparer, the items are sorted and deduplicated, which
        // ConstructRootFromSortedArray bounds (R34.27's deviation).
        [Requires("(comparer == null ? Comparer<T>.Default : comparer) == collection.SpecComparer || " +
                  "!SpecSortDedupe.ComparerEquals(comparer == null ? Comparer<T>.Default : comparer, collection.SpecComparer)")]
        [Requires("Pal.Implies((comparer == null ? Comparer<T>.Default : comparer) != collection.SpecComparer, 2 * collection.SpecItems.Length + 2 <= 1073741824)")]
        [Ensures("@this.SpecComparer == (comparer == null ? Comparer<T>.Default : comparer)")]
        [Ensures("SpecSortDedupe.SetOf(@this.SpecComparer, @this.SpecItems, collection.SpecItems)")]
        [Ensures("Pal.Implies(@this.SpecComparer == collection.SpecComparer, @this.SpecItems == collection.SpecItems)")]
        [Ensures("collection.SpecItems == Pal.Old(collection.SpecItems)")]
        [Ensures("collection.SpecComparer == Pal.Old(collection.SpecComparer)")]
        public SortedSet([Exactly(typeof(SortedSet<>))] IEnumerable<T> collection, IComparer<T>? comparer)
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
#if PAL
                    Ghost<Node?> previousRoot = root;
                    Ghost<SortedSetLabels<T>> clonedSource = sortedSet.SpecLabels;
                    Node cloneRoot = sortedSet.root;
                    SortedSetOwnershipProof.ReadSet(clonedSource, Perm.Full);
                    root = cloneRoot.DeepClone(this.count);
#else
                    root = sortedSet.root.DeepClone(this.count);
#endif
#if PAL
                    SortedSetOwnershipProof.EndSet(clonedSource, Perm.Full);
                    Ghost<SortedSetLabels<T>> clonedLabels = SortedSetConstructionProof.Label(root,
                        SortedSetOwnership.Values(clonedSource.Value), Perm.Full);
                    SortedSetConstructionProof.Adopt(previousRoot, root, ownershipState, clonedLabels);
                    ownershipState = SortedSetConstruction.Adopted(ownershipState, clonedLabels);
#endif
                }
                SetOfSelf(((SortedSet<T>)collection).SpecComparer, ((SortedSet<T>)collection).SpecItems);
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
                DedupeInit(comparer, ((SortedSet<T>)collection).SpecItems, Pal.Contents(elements), count);

                // Overwrite duplicates while shifting the distinct elements towards
                // the front of the array.
                int index = 1;
                for (int i = 1; i < count; i++)
                {
                    Pal.Invariant(comparer == this.comparer && count <= elements.Length && elements.Length <= 1073741824);
                    Pal.Invariant(SpecSortDedupe.DedupeInv(comparer, ((SortedSet<T>)collection).SpecItems, Pal.Contents(elements), i, index, count));
                    DedupeStep(comparer, ((SortedSet<T>)collection).SpecItems, Pal.Contents(elements), i, index, count);
                    if (comparer.Compare(elements[i], elements[i - 1]) != 0)
                    {
                        elements[index++] = elements[i];
                    }
                }

                DedupeDone(comparer, ((SortedSet<T>)collection).SpecItems, Pal.Contents(elements), index, count);
                count = index;
#if PAL
                Ghost<Node?> previousRoot = root;
                Ghost<Seq<T>> builtItems = Pal.Contents(elements);
                SortedSetConstructionProof.Empty<T>(null);
#endif
                root = ConstructRootFromSortedArray(elements, 0, count - 1, null);
#if PAL
                Ghost<SortedSetLabels<T>> builtLabels = SortedSetConstructionProof.Label(root,
                    SpecSearchTree.Build(builtItems.Value, 0, count - 1, SpecTree.Leaf<(T, bool)>()), Perm.Full);
                Pal.Assert(SpecSortDedupe.SetOf(comparer, SpecSearchTree.Keys(SortedSetOwnership.Values(builtLabels.Value)), ((SortedSet<T>)collection).SpecItems));
                Pal.Assert(Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Values(builtLabels.Value))) && count == SpecSearchTree.Keys(SortedSetOwnership.Values(builtLabels.Value)).Length);
                Pal.Assert(SpecSearchTree.IsRedBlack(SortedSetOwnership.Values(builtLabels.Value)));
                SortedSetConstructionProof.Adopt(previousRoot, root, ownershipState, builtLabels);
                ownershipState = SortedSetConstruction.Adopted(ownershipState, builtLabels);
                Pal.Assert(this.comparer != null);
#endif
                this.count = count;
            }
        }

        [Lemma]
        [Requires("Pal.StrictlySorted(c, s)")]
        [Ensures("SpecSortDedupe.SetOf(c, s, s)")]
        [PulseBody("Pulse.Lib.CSharp.SortDedupe.set_of_self $(c) $(s)")]
        [Conditional("PAL")]
        private static void SetOfSelf(IComparer<T> c, Seq<T> s) { }

        [Lemma]
        [Requires("1 <= n && n <= a.Length && Pal.Permutation(src, Pal.Slice(a, 0, n)) && SpecSortDedupe.SortedIn(c, a, 0, n)")]
        [Ensures("SpecSortDedupe.DedupeInv(c, src, a, 1, 1, n)")]
        [PulseBody("Pulse.Lib.CSharp.SortDedupe.dedupe_init $(c) $(src) $(a) $(n)")]
        [Conditional("PAL")]
        private static void DedupeInit(IComparer<T> c, Seq<T> src, Seq<T> a, SpecInt n) { }

        [Lemma]
        [Requires("SpecSortDedupe.DedupeInv(c, src, a, i, index, n) && i < n")]
        [Ensures("Pal.Implies(Pal.Compare(c, a[i], a[i - 1]) != 0, SpecSortDedupe.DedupeInv(c, src, SpecSortDedupe.Update(a, index, a[i]), i + 1, index + 1, n))")]
        [Ensures("Pal.Implies(Pal.Compare(c, a[i], a[i - 1]) == 0, SpecSortDedupe.DedupeInv(c, src, a, i + 1, index, n))")]
        [PulseBody("Pulse.Lib.CSharp.SortDedupe.dedupe_step $(c) $(src) $(a) $(i) $(index) $(n)")]
        [Conditional("PAL")]
        private static void DedupeStep(IComparer<T> c, Seq<T> src, Seq<T> a, SpecInt i, SpecInt index, SpecInt n) { }

        [Lemma]
        [Requires("SpecSortDedupe.DedupeInv(c, src, a, n, index, n)")]
        [Ensures("SpecSortDedupe.SetOf(c, Pal.Slice(a, 0, index), src)")]
        [PulseBody("Pulse.Lib.CSharp.SortDedupe.dedupe_done $(c) $(src) $(a) $(index) $(n)")]
        [Conditional("PAL")]
        private static void DedupeDone(IComparer<T> c, Seq<T> src, Seq<T> a, SpecInt index, SpecInt n) { }

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        [EditorBrowsable(EditorBrowsableState.Never)]
        protected SortedSet(SerializationInfo info, StreamingContext context) => siInfo = info;

        #endregion

        #region Bulk operation helpers

        // Each element of `collection` is looked up and added under this set's comparer, so the
        // contract requires the same comparer (doc/translation.md R27.47); the counts bound
        // the size the set can reach, so that `Add` cannot overflow `count`.
        [Requires("@this.SpecComparer == collection.SpecComparer")]
        [Requires("@this.SpecItems.Length + collection.SpecItems.Length <= int.MaxValue")]
        [Ensures("@this.SpecItems == SpecSetOps.AddAll(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), Pal.Old(collection.SpecItems))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer) && collection.SpecItems == Pal.Old(collection.SpecItems) && collection.SpecComparer == Pal.Old(collection.SpecComparer)")]
        [Rlimit(8)]
        private void AddAllElements([Exactly(typeof(SortedSet<>))] IEnumerable<T> collection)
        {
            foreach (T item in collection)
            {
                Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecReady &&
                              Pal.Enumerator<Enumerator>(item).SpecPending ==
                                  Pal.Slice(((SortedSet<T>)collection).SpecItems, ((SortedSet<T>)collection).SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length, ((SortedSet<T>)collection).SpecItems.Length) &&
                              this.SpecComparer == Pal.Old(this.SpecComparer) &&
                              this.SpecItems == SpecSetOps.AddAll(Pal.Old(this.SpecComparer), Pal.Old(this.SpecItems),
                                  Pal.Slice(((SortedSet<T>)collection).SpecItems, 0, ((SortedSet<T>)collection).SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length)));
                Pal.Decreases(Pal.Enumerator<Enumerator>(item).SpecPending.Length);
                SpecSetOps.AddAllStep(Pal.Old(this.SpecComparer), Pal.Old(this.SpecItems), ((SortedSet<T>)collection).SpecItems,
                    ((SortedSet<T>)collection).SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                SpecSetOps.AddAllLength(Pal.Old(this.SpecComparer), Pal.Old(this.SpecItems), ((SortedSet<T>)collection).SpecItems,
                    ((SortedSet<T>)collection).SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                if (!Contains(item))
                {
                    Add(item);
                }
            }
            SpecSetOps.AddAllWhole(Pal.Old(this.SpecComparer), Pal.Old(this.SpecItems), ((SortedSet<T>)collection).SpecItems);
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
        // pal: R32.11. It calls `action` at most once per item: fewer times than any bound the
        // caller passes that is at least `Count`.
        [Requires("@this.SpecItems.Length <= Pal.CallBound(action)")]
        [Ensures("SpecWalk.Walked(@this.SpecItems, Pal.Trace<(T, bool), bool>(action), Result)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Rlimit(8)]
        [Wrapping]
        [Frac("p")]
        internal virtual bool InOrderTreeWalk([Callback("SortedSetNodeSnapshot<T> snapshot", "SortedSetOwnership.Raw(argument, snapshot, permission)", "SortedSetOwnership.Entry(snapshot)", Bounded = true)] TreeWalkPredicate<T> action)
        {
#if PAL
            Ghost<SortedSetLabels<T>> labels = this.SpecLabels;
            Ghost<Seq<T>> items = this.SpecItems;
            Ghost<SortedSetSnapshot<T>> snapshot = SortedSetOwnership.Snapshot(this.SpecSnapshot);
            SortedSetOwnershipProof.RootFacts(labels);
#endif
            if (root == null)
            {
                return true;
            }

            // The maximum height of a red-black tree is 2 * log2(n+1).
            // See page 264 of "Introduction to algorithms" by Thomas H. Cormen
            // Note: It's not strictly necessary to provide the stack capacity, but we don't
            // want the stack to unnecessarily allocate arrays as it grows.

            var stack = new Stack<Node?>(2 * (int)Log2(Count + 1));
            Node? current = root;
#if PAL
            SortedSetOwnershipProof.ReadOwner(root, ownershipState, labels, Pal.Permission());
            SortedSetWalkProof.Empty(false, labels, stack.Items);
#endif

            while (current != null)
            {
#if PAL
                Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                Pal.Invariant(SortedSetOwnership.OwnerLease(root, ownershipState, labels.Value, Pal.Permission()));
                Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, snapshot.Value));
                Pal.Invariant(root == SortedSetOwnership.Top(labels.Value) &&
                    Pal.Same(SortedSetOwnership.Active(ownershipState), labels.Value) &&
                    comparer == Pal.Old(this.SpecComparer) && version == Pal.Old(this.SpecVersion));
                Pal.Invariant((current == null || SortedSetOwnership.Member(labels.Value, current)) &&
                              SortedSetWalk.Walkable(labels.Value, stack.Items) &&
                              items.Value.Length == count &&
                              Pal.Trace<(T, bool), bool>(action).Length == 0 &&
                              Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(labels.Value, current)),
                                         SortedSetWalk.Pending(false, labels.Value, stack.Items)) == items.Value);
                SortedSetWalkProof.Descend(false, labels, stack.Items, current);
                Pal.Assert(stack.Items.Length < count);
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
#endif
                stack.Push(current);
                current = current.Left;
#if PAL
                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
            }

            while (stack.Count != 0)
            {
#if PAL
                Pal.Decreases(items.Value.Length - Pal.Trace<(T, bool), bool>(action).Length);
                Pal.Invariant(SortedSetOwnership.OwnerLease(root, ownershipState, labels.Value, Pal.Permission()));
                Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, snapshot.Value));
                Pal.Invariant(root == SortedSetOwnership.Top(labels.Value) &&
                    Pal.Same(SortedSetOwnership.Active(ownershipState), labels.Value) &&
                    comparer == Pal.Old(this.SpecComparer) && version == Pal.Old(this.SpecVersion));
                Pal.Invariant(SortedSetWalk.Walkable(labels.Value, stack.Items) &&
                              0 <= Pal.Trace<(T, bool), bool>(action).Length && Pal.Trace<(T, bool), bool>(action).Length <= count &&
                              items.Value.Length == count &&
                              (Pal.Returned()
                                  ? !Pal.ReturnValue<bool>() &&
                                    SpecWalk.Walked(items.Value, Pal.Trace<(T, bool), bool>(action), false)
                                  : SpecWalk.Visited(items.Value, Pal.Trace<(T, bool), bool>(action)) &&
                                    SortedSetWalk.Pending(false, labels.Value, stack.Items) ==
                                    Pal.Slice(items.Value, Pal.Trace<(T, bool), bool>(action).Length, count)));
                SortedSetWalkProof.PopAt(false, labels, stack.Items, items, (SpecInt)Pal.Trace<(T, bool), bool>(action).Length);
#endif
                current = stack.Pop();
#if PAL
                SortedSetOwnershipProof.ReadOwner(root, ownershipState, labels, Pal.Permission());
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                Ghost<Seq<((T, bool), bool)>> before = Pal.Trace<(T, bool), bool>(action);
#endif
                if (!action(current!))
                {
#if PAL
                    SortedSetWalkProof.TraceStep(items, before, Pal.Trace<(T, bool), bool>(action), false);
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
                    return false;
                }
#if PAL
                else
                {
                    SortedSetWalkProof.TraceStep(items, before, Pal.Trace<(T, bool), bool>(action), true);
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                }
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
#endif

                Node? node = current!.Right;
#if PAL
                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
                while (node != null)
                {
#if PAL
                    Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, node).Size);
                    Pal.Invariant(SortedSetOwnership.OwnerLease(root, ownershipState, labels.Value, Pal.Permission()));
                    Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, snapshot.Value));
                    Pal.Invariant(root == SortedSetOwnership.Top(labels.Value) &&
                        Pal.Same(SortedSetOwnership.Active(ownershipState), labels.Value) &&
                        comparer == Pal.Old(this.SpecComparer) && version == Pal.Old(this.SpecVersion));
                    Pal.Invariant((node == null || SortedSetOwnership.Member(labels.Value, node)) &&
                                  SortedSetWalk.Walkable(labels.Value, stack.Items) &&
                                  0 < Pal.Trace<(T, bool), bool>(action).Length && Pal.Trace<(T, bool), bool>(action).Length <= count &&
                                  items.Value.Length == count &&
                                  SpecWalk.Visited(items.Value, Pal.Trace<(T, bool), bool>(action)) &&
                                  Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(labels.Value, node)),
                                             SortedSetWalk.Pending(false, labels.Value, stack.Items)) ==
                                  Pal.Slice(items.Value, Pal.Trace<(T, bool), bool>(action).Length, count));
                    SortedSetWalkProof.Descend(false, labels, stack.Items, node);
                    Pal.Assert(stack.Items.Length < count - Pal.Trace<(T, bool), bool>(action).Length);
                    SortedSetOwnershipProof.OpenRead(labels, node, Pal.Permission());
#endif
                    stack.Push(node);
                    node = node.Left;
#if PAL
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
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
        [Rlimit(8)]
        [Wrapping]
        [Frac("p")]
        internal virtual bool BreadthFirstTreeWalk([Callback("SortedSetNodeSnapshot<T> snapshot", "SortedSetOwnership.Raw(argument, snapshot, permission)", "SortedSetOwnership.Entry(snapshot)")] TreeWalkPredicate<T> action)
        {
#if PAL
            Ghost<SortedSetLabels<T>> labels = this.SpecLabels;
            Ghost<Seq<T>> items = this.SpecItems;
            Ghost<SortedSetSnapshot<T>> snapshot = SortedSetOwnership.Snapshot(this.SpecSnapshot);
            SortedSetOwnershipProof.RootFacts(labels);
#endif
            if (root == null)
            {
                return true;
            }

            var processQueue = new Queue<Node?>();
            processQueue.Enqueue(root);
#if PAL
            SortedSetOwnershipProof.ReadOwner(root, ownershipState, labels, Pal.Permission());
            SortedSetBreadthProof.Start(labels, root, processQueue.Items, items, Pal.Trace<(T, bool), bool>(action));
#endif

            Node? current;
            while (processQueue.Count != 0)
            {
#if PAL
                Pal.Decreases(items.Value.Length - Pal.Trace<(T, bool), bool>(action).Length);
                Pal.Invariant(SortedSetOwnership.OwnerLease(root, ownershipState, labels.Value, Pal.Permission()));
                Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, snapshot.Value));
                Pal.Invariant(root == SortedSetOwnership.Top(labels.Value) &&
                    Pal.Same(SortedSetOwnership.Active(ownershipState), labels.Value) &&
                    comparer == Pal.Old(this.SpecComparer) && version == Pal.Old(this.SpecVersion));
                Pal.Invariant(SortedSetWalk.Walkable(labels.Value, processQueue.Items) &&
                              0 <= Pal.Trace<(T, bool), bool>(action).Length &&
                              items.Value.Length == count &&
                              (Pal.Returned()
                                  ? !Pal.ReturnValue<bool>() &&
                                    SpecWalk.BfWalked(items.Value, Pal.Trace<(T, bool), bool>(action), false)
                                  : SpecWalk.BfVisited(items.Value, Pal.Trace<(T, bool), bool>(action),
                                                       SortedSetBreadth.Pending(labels.Value, processQueue.Items))));
                Ghost<Seq<Node?>> q0 = processQueue.Items;
                SortedSetBreadthProof.Dequeue(labels, q0, items, Pal.Trace<(T, bool), bool>(action));
#endif
                current = processQueue.Dequeue();
#if PAL
                SortedSetOwnershipProof.ReadOwner(root, ownershipState, labels, Pal.Permission());
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                Pal.Assert(Pal.Trace<(T, bool), bool>(action).Length < int.MaxValue);
#endif
                if (!action(current!))
                {
#if PAL
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
                    return false;
                }
#if PAL
                else
                {
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                }
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
#endif

                Pal.Assert(processQueue.SpecCount < int.MaxValue);
                if (current!.Left != null)
                {
                    processQueue.Enqueue(current!.Left);
                }
                Pal.Assert(processQueue.SpecCount < int.MaxValue);
                if (current!.Right != null)
                {
                    processQueue.Enqueue(current!.Right);
                }
#if PAL
                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                Pal.Assert(processQueue.Items == SortedSetBreadth.Next(labels.Value, q0.Value));
#endif
            }

            return true;
        }

        #endregion

        #region Properties

        [Ensures("Result == @this.SpecItems.Length")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Requires("@this.SpecCoherent && @this.SpecCountOk", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Result == SpecRangeWalk.Filter(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems).Length", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("@this.SpecCoherent && @this.SpecCountOk && @this.version == @this._underlying.SpecVersion && @this.SpecRootOk && @this._countVersion == @this._underlying.SpecVersion", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
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
        [Ensures("Result == @this.comparer", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
        public IComparer<T> Comparer => comparer;

        bool ICollection<T>.IsReadOnly => false;

        bool ICollection.IsSynchronized => false;

        object ICollection.SyncRoot => this;

        #endregion

        #region Subclass helpers

        // Virtual function for TreeSubSet, which may need to update its count.
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Requires("@this.SpecCoherent && Pal.Implies(updateCount, @this.SpecCountOk)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("@this.SpecCoherent && @this.version == @this._underlying.SpecVersion && @this.SpecRootOk", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Implies(updateCount, @this.count == SpecRangeWalk.Filter(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems).Length && @this._countVersion == @this._underlying.SpecVersion)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Implies(!updateCount, @this.count == Pal.Old(@this.count) && @this._countVersion == Pal.Old(@this._countVersion))", At = typeof(SortedSet<>.TreeSubSet))]
        internal virtual void VersionCheck(bool updateCount = false) { }
        // Virtual function for TreeSubSet, which may need the count variable of the parent set.
        [Ensures("Result == @this.SpecItems.Length")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Result == @this._underlying.SpecItems.Length", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("@this._underlying.SpecNodes == Pal.Old(@this._underlying.SpecNodes) && @this._underlying.SpecComparer == Pal.Old(@this._underlying.SpecComparer)", At = typeof(SortedSet<>.TreeSubSet))]
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
        [Ensures("@this.SpecVersion == SpecWrap.Int32(Pal.Old(@this.SpecVersion) + 1)")]
        [Throws(typeof(ArgumentException), "Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0", At = typeof(TreeSet<>))]
        public bool Add(T item) => AddIfNotPresent(item); // Hack so the implementation can be made virtual

        void ICollection<T>.Add(T item) => Add(item);

        [Requires("@this.SpecItems.Length < int.MaxValue")]
        [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) < 0)")]
        [Ensures("Pal.Implies(Result, @this.SpecItems == SpecTopDown.Inserted(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item))")]
        [Ensures("Pal.Implies(!Result, @this.SpecItems == Pal.Old(@this.SpecItems))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecVersion == SpecWrap.Int32(Pal.Old(@this.SpecVersion) + 1)")]
        internal virtual bool AddIfNotPresent(T item)
        {
#if PAL
            Ghost<SortedSetLabels<T>> original = this.SpecLabels;
            Ghost<Seq<T>> k0 = this.SpecItems;
#endif
            if (root == null)
            {
#if PAL
                SortedSetEditProof.BeginOwner(root, ownershipState);
                SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), original);
                SortedSetLeafProof.ReleaseEmpty(original);
#endif
                // The tree is empty and this is the first item.
                root = new Node(item, NodeColor.Black);
                count = 1;
                version++;
#if PAL
                SortedSetLeafProof.MakeBlack(root, item);
                SortedSetInsert.Singleton(comparer, item, root);
                Ghost<SortedSetLabels<T>> singleton = SortedSetLeaf.Black(root, item);
                SortedSetEditProof.Change<T>(SortedSetLeaf.Black(root, item), singleton);
                SortedSetInsert.ResultFacts(comparer, k0.Value, item, root, singleton.Value);
                SortedSetEditProof.EndOwner(root, ownershipState, singleton);
                ownershipState = SortedSetEdit.ReplaceState(ownershipState, singleton);
#endif
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

#if PAL
            SortedSetInsert.Start(comparer, item, original.Value);
            IComparer<T> ordering = comparer;
            SortedSetOwnershipState<T> progress = ownershipState;
#endif

            int order = 0;
            while (current != null)
            {
#if PAL
                Pal.Decreases(SortedSetInsert.Measure(ordering, item, SortedSetOwnership.Active(progress), current));
                Pal.Invariant(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                Pal.Invariant(Pal.Same(SortedSetOwnership.Active(progress), SortedSetOwnership.Active(ownershipState)));
                Pal.Invariant(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) && version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
                Pal.Invariant(Pal.Implies(!Pal.Returned(),
                    SortedSetInsert.Inv(comparer, k0.Value, item, SortedSetOwnership.Active(ownershipState),
                        current, parent, grandParent, greatGrandParent, order)));
                Pal.Invariant(Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() &&
                    Pal.KeyIndex(comparer, k0.Value, item) >= 0 &&
                    SortedSetInsert.Complete(comparer, k0.Value, item, root, SortedSetOwnership.Active(ownershipState))));
                Ghost<SortedSetLabels<T>> before = SortedSetOwnership.Active(ownershipState);
                Ghost<SpecInt> m0 = SortedSetInsert.Measure(comparer, item, before.Value, current);
                Ghost<int> order0 = order;
                SortedSetInsert.AtCur(comparer, k0.Value, item, before.Value, current, parent, grandParent, greatGrandParent, order);
                SortedSetEditProof.BeginOwner(root, ownershipState);
                SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), before);
                SortedSetOwnershipProof.OpenRead(before, current, Perm.Full);
#endif
                order = comparer.Compare(item, current.Item);
#if PAL
                SortedSetOwnershipProof.CloseRead(before, Perm.Full);
                SortedSetInsert.Look(comparer, k0.Value, item, before.Value, current, parent, grandParent, greatGrandParent, order0.Value, order);
#endif
                if (order == 0)
                {
                    // We could have changed root node to red during the search process.
                    // We need to set it to black before we return.
#if PAL
                    SortedSetInsert.Finish(comparer, k0.Value, item, before.Value);
                    SortedSetOwnershipProof.RootFacts(before);
                    SortedSetEditProof.OpenColor(before, root);
#endif
                    root.ColorBlack();
#if PAL
                    SortedSetEditProof.CloseBlack(before, root);
                    SortedSetBalance.TopColor(before.Value, root, false);
                    Ghost<SortedSetLabels<T>> done = SortedSetInsert.Black(before.Value);
                    SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(before.Value, root, false), done);
                    SortedSetInsert.ResultFacts(comparer, k0.Value, item, root, done.Value);
                    SortedSetEditProof.EndOwner(root, ownershipState, done);
                    ownershipState = SortedSetEdit.ReplaceState(ownershipState, done);
                    progress = ownershipState;
#endif
                    return false;
                }
#if PAL
                else
                {
                    SortedSetEditProof.EndOwner(root, ownershipState, before);
                    ownershipState = SortedSetEdit.ReplaceState(ownershipState, before);
                }
                Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                Pal.Join(Pal.Same(SortedSetOwnership.Active(progress), SortedSetOwnership.Active(ownershipState)));
                Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) &&
                    version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
                Pal.Join(Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() &&
                    Pal.KeyIndex(comparer, k0.Value, item) >= 0 &&
                    SortedSetInsert.Complete(comparer, k0.Value, item, root, SortedSetOwnership.Active(ownershipState))));
                Pal.Join(Pal.Implies(!Pal.Returned(),
                    order != 0 && Pal.Same(SortedSetOwnership.Active(ownershipState), before.Value)));
                SortedSetEditProof.BeginOwner(root, ownershipState);
                SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), before);
                SortedSetFrontierProof.OpenRead(before, current);
                SortedSetFrontier.ReadFacts(SortedSetEdit.Sub(before.Value, current));
#endif

                // Split a 4-node into two 2-nodes.
                if (current.Is4Node)
                {
#if PAL
                    SortedSetFrontierProof.CloseRead(before, current);
                    SortedSetFrontierProof.OpenSplit(before, current);
#endif
                    current.Split4Node();
#if PAL
                    SortedSetFrontierProof.CloseSplit(before, current);
                    SortedSetInsert.SplitStep(comparer, k0.Value, item, before.Value, current, parent, grandParent, greatGrandParent, order0.Value, order);
                    Ghost<SortedSetLabels<T>> split = SortedSetFrontier.Split(before.Value, current);
                    SortedSetEditProof.Change<T>(SortedSetFrontier.Split(before.Value, current), split);
                    SortedSetFrontierProof.OpenOptional(split, parent);
#endif
                    // We could have introduced two consecutive red nodes after split. Fix that by rotation.
                    if (Node.IsNonNullRed(parent))
                    {
#if PAL
                        SortedSetFrontierProof.CloseOptional(split, parent);
                        SortedSetEditProof.EndOwner(root, ownershipState, split);
                        ownershipState = SortedSetEdit.ReplaceState(ownershipState, split);
                        SortedSetInsert.BalanceNodes(split.Value, current, parent, grandParent, greatGrandParent);
#endif
                        InsertionBalance(current, ref parent!, grandParent!, greatGrandParent!);
                    }
#if PAL
                    else
                    {
                        SortedSetFrontierProof.CloseOptional(split, parent);
                        SortedSetEditProof.EndOwner(root, ownershipState, split);
                        ownershipState = SortedSetEdit.ReplaceState(ownershipState, split);
                    }
                    Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                    Pal.Join(SortedSetInsert.Ready(comparer, k0.Value, item, SortedSetOwnership.Active(ownershipState),
                        current, parent, grandParent, order, m0.Value));
                    Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) &&
                        version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
#endif
                }
#if PAL
                else
                {
                    SortedSetFrontierProof.CloseRead(before, current);
                    SortedSetEditProof.EndOwner(root, ownershipState, before);
                    ownershipState = SortedSetEdit.ReplaceState(ownershipState, before);
                }
                Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                Pal.Join(SortedSetInsert.Ready(comparer, k0.Value, item, SortedSetOwnership.Active(ownershipState),
                    current, parent, grandParent, order, m0.Value));
                Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) &&
                    version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
                Ghost<SortedSetLabels<T>> after = SortedSetOwnership.Active(ownershipState);
                SortedSetEditProof.BeginOwner(root, ownershipState);
                SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), after);
                SortedSetOwnershipProof.OpenTreePoint(after, current, Perm.Full);
#endif

                greatGrandParent = grandParent;
                grandParent = parent;
                parent = current;
                current = (order < 0) ? current.Left : current.Right;
#if PAL
                SortedSetOwnershipProof.CloseTreePoint(after, Perm.Full);
                SortedSetInsert.Advance(comparer, k0.Value, item, after.Value, parent, grandParent, greatGrandParent, current, order, m0.Value);
                SortedSetEditProof.EndOwner(root, ownershipState, after);
                ownershipState = SortedSetEdit.ReplaceState(ownershipState, after);
                progress = ownershipState;
#endif
            }

#if PAL
            Ghost<SortedSetLabels<T>> descent = SortedSetOwnership.Active(ownershipState);
            SortedSetInsert.AtEnd(comparer, k0.Value, item, descent.Value, parent, grandParent, greatGrandParent, order);
            SortedSetEditProof.BeginOwner(root, ownershipState);
            SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), descent);
#endif
            Debug.Assert(parent != null);
            // We're ready to insert the new node.
            Node node = new Node(item, NodeColor.Red);
#if PAL
            SortedSetLeafProof.MakeRed(node, item);
            SortedSetLeafProof.Fresh(descent, node, item);
            SortedSetInsert.Linked(comparer, k0.Value, item, descent.Value, node, parent, grandParent, greatGrandParent, order);
            Ghost<SortedSetLabels<T>> linked = SortedSetLeaf.Linked(descent.Value, parent, node, item, order > 0);
            SortedSetLeafProof.OpenLink(descent, parent);
#endif
            if (order > 0)
            {
                parent.Right = node;
#if PAL
                SortedSetLeafProof.CloseRight(descent, parent, node, item);
                SortedSetEditProof.Change<T>(SortedSetLeaf.Linked(descent.Value, parent, node, item, true), linked);
#endif
            }
            else
            {
                parent.Left = node;
#if PAL
                SortedSetLeafProof.CloseLeft(descent, parent, node, item);
                SortedSetEditProof.Change<T>(SortedSetLeaf.Linked(descent.Value, parent, node, item, false), linked);
#endif
            }
#if PAL
            Pal.Join(SortedSetOwnership.Owns(linked.Value, Perm.Full));
            Pal.Join(SortedSetEdit.Retained(ownershipState));
            Pal.Join(root == SortedSetOwnership.Top(linked.Value));
            Pal.Join(Pal.Same(linked.Value, SortedSetLeaf.Linked(descent.Value, parent, node, item, order > 0)));
            Pal.Join(SortedSetInsert.LinkedResult(comparer, k0.Value, item, descent.Value,
                node, parent, grandParent, greatGrandParent, order));
            Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) &&
                version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
            SortedSetOwnershipProof.OpenRead(linked, parent, Perm.Full);
#endif

            // The new node will be red, so we will need to adjust colors if its parent is also red.
            if (parent.IsRed)
            {
#if PAL
                SortedSetOwnershipProof.CloseRead(linked, Perm.Full);
                SortedSetEditProof.EndOwner(root, ownershipState, linked);
                ownershipState = SortedSetEdit.ReplaceState(ownershipState, linked);
                SortedSetInsert.BalanceNodes(linked.Value, node, parent, grandParent, greatGrandParent);
#endif
                InsertionBalance(node, ref parent!, grandParent!, greatGrandParent!);
            }
#if PAL
            else
            {
                SortedSetOwnershipProof.CloseRead(linked, Perm.Full);
                SortedSetEditProof.EndOwner(root, ownershipState, linked);
                ownershipState = SortedSetEdit.ReplaceState(ownershipState, linked);
            }
            Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
            Pal.Join(SortedSetInsert.Ok(comparer, SortedSetInsert.Expected(comparer, k0.Value, item), SortedSetOwnership.Active(ownershipState)));
            Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) &&
                version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1) && Pal.KeyIndex(comparer, k0.Value, item) < 0);
            Ghost<SortedSetLabels<T>> final = SortedSetOwnership.Active(ownershipState);
            SortedSetInsert.Finish(comparer, k0.Value, item, final.Value);
            SortedSetInsert.NewRoot(comparer, k0.Value, item, final.Value);
            SortedSetOwnershipProof.RootFacts(final);
            SortedSetEditProof.BeginOwner(root, ownershipState);
            SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), final);
            SortedSetEditProof.OpenColor(final, root);
#endif

            // The root node is always black.
            root.ColorBlack();
#if PAL
            SortedSetEditProof.CloseBlack(final, root);
            SortedSetBalance.TopColor(final.Value, root, false);
            Ghost<SortedSetLabels<T>> complete = SortedSetInsert.Black(final.Value);
            SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(final.Value, root, false), complete);
            SortedSetInsert.ResultFacts(comparer, k0.Value, item, root, complete.Value);
            SortedSetEditProof.EndOwner(root, ownershipState, complete);
            ownershipState = SortedSetEdit.ReplaceState(ownershipState, complete);
            Pal.Assert(SortedSetOwnership.Valid(root, ownershipState, comparer, count + 1, version));
#endif
            ++count;
            return true;
        }

        [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) >= 0)")]
        [Ensures("@this.SpecItems == SpecTopDownRemove.Removed(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(Pal.Old(@this.SpecNodes).Size == 0, @this.SpecNodes == Pal.Old(@this.SpecNodes) && @this.SpecVersion == Pal.Old(@this.SpecVersion))")]
        [Ensures("Pal.Implies(Pal.Old(@this.SpecNodes).Size != 0, @this.SpecVersion == SpecWrap.Int32(Pal.Old(@this.SpecVersion) + 1))")]
        public bool Remove(T item) => DoRemove(item); // Hack so the implementation can be made virtual

        [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) >= 0)")]
        [Ensures("@this.SpecItems == SpecTopDownRemove.Removed(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(Pal.Old(@this.SpecNodes).Size == 0, @this.SpecNodes == Pal.Old(@this.SpecNodes) && @this.SpecVersion == Pal.Old(@this.SpecVersion))")]
        [Ensures("Pal.Implies(Pal.Old(@this.SpecNodes).Size != 0, @this.SpecVersion == SpecWrap.Int32(Pal.Old(@this.SpecVersion) + 1))")]
        [Rlimit(10)]
        internal virtual bool DoRemove(T item)
        {
#if PAL
            Ghost<SortedSetLabels<T>> original = this.SpecLabels;
            Ghost<Seq<T>> k0 = this.SpecItems;
#endif
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
#if PAL
            SortedSetRemove.Start(comparer, item, original.Value);
            SortedSetOwnershipState<T> progress = ownershipState;
#endif
            while (current != null)
            {
#if PAL
                Pal.Decreases(SortedSetRemove.Measure(SortedSetOwnership.Active(progress), current));
                Pal.Invariant(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                Pal.Invariant(Pal.Same(SortedSetOwnership.Active(progress), SortedSetOwnership.Active(ownershipState)));
                Pal.Invariant(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) && version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
                Pal.Invariant(SortedSetRemove.Inv(comparer, k0.Value, item, SortedSetOwnership.Active(ownershipState),
                    current, parent, grandParent, match, parentOfMatch, foundMatch));
                Ghost<SortedSetLabels<T>> before = SortedSetOwnership.Active(ownershipState);
                Ghost<SpecInt> m0 = SortedSetRemove.Measure(before.Value, current);
                SortedSetRemove.AtCur(comparer, k0.Value, item, before.Value, current, parent, grandParent, match, parentOfMatch, foundMatch);
                SortedSetEditProof.BeginOwner(root, ownershipState);
                SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), before);
                SortedSetFrontierProof.OpenRead(before, current);
                SortedSetFrontier.Read2Facts(SortedSetEdit.Sub(before.Value, current));
#endif
                if (current.Is2Node)
                {
#if PAL
                    SortedSetFrontierProof.CloseRead(before, current);
#endif
                    // Fix up 2-node
                    if (parent == null)
                    {
                        // `current` is the root. Mark it red.
#if PAL
                        SortedSetEditProof.OpenColor(before, current);
#endif
                        current.ColorRed();
#if PAL
                        SortedSetEditProof.CloseRed(before, current);
                        SortedSetRemove.Root(comparer, k0.Value, item, before.Value, current, parent, grandParent, match, parentOfMatch, foundMatch);
                        Ghost<SortedSetLabels<T>> redRoot = SortedSetEdit.Recolor(before.Value, current, true);
                        SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(before.Value, current, true), redRoot);
                        SortedSetEditProof.EndOwner(root, ownershipState, redRoot);
                        ownershipState = SortedSetEdit.ReplaceState(ownershipState, redRoot);
#endif
                    }
                    else
                    {
#if PAL
                        SortedSetRemove.AtSibling(comparer, k0.Value, item, before.Value, current, parent, grandParent, match, parentOfMatch, foundMatch);
                        SortedSetOwnershipProof.OpenRead(before, parent, Perm.Full);
#endif
                        Node sibling = parent.GetSibling(current);
#if PAL
                        SortedSetOwnershipProof.CloseRead(before, Perm.Full);
                        SortedSetOwnershipProof.OpenRead(before, sibling, Perm.Full);
#endif
                        if (sibling.IsRed)
                        {
#if PAL
                            SortedSetOwnershipProof.CloseRead(before, Perm.Full);
                            SortedSetRemove.Lift(comparer, k0.Value, item, before.Value, current, parent, grandParent, match, parentOfMatch, foundMatch);
                            Ghost<SortedSetLabels<T>> sub = SortedSetEdit.Sub(before.Value, parent);
                            SortedSetLift.Layout(sub.Value, sibling);
                            SortedSetOwnershipProof.OpenRead(before, parent, Perm.Full);
#endif
                            // If parent is a 3-node, flip the orientation of the red link.
                            // We can achieve this by a single rotation.
                            // This case is converted to one of the other cases below.
                            Debug.Assert(parent.IsBlack);
                            if (parent.Right == sibling)
                            {
#if PAL
                                SortedSetOwnershipProof.CloseRead(before, Perm.Full);
                                SortedSetEditProof.Cut(before, parent);
                                SortedSetEditProof.Change<T>(SortedSetEdit.Sub(before.Value, parent), sub);
                                SortedSetBalanceProof.OpenLeft(parent, sub);
#endif
                                parent.RotateLeft();
#if PAL
                                SortedSetBalanceProof.CloseIgnoredLeft(parent, sub);
                                SortedSetEditProof.Change<T>(SortedSetBalance.Single(sub.Value, true), SortedSetLift.Rotated(sub.Value, sibling));
#endif
                            }
                            else
                            {
#if PAL
                                SortedSetOwnershipProof.CloseRead(before, Perm.Full);
                                SortedSetEditProof.Cut(before, parent);
                                SortedSetEditProof.Change<T>(SortedSetEdit.Sub(before.Value, parent), sub);
                                SortedSetBalanceProof.OpenRight(parent, sub);
#endif
                                parent.RotateRight();
#if PAL
                                SortedSetBalanceProof.CloseIgnoredRight(parent, sub);
                                SortedSetEditProof.Change<T>(SortedSetBalance.Single(sub.Value, false), SortedSetLift.Rotated(sub.Value, sibling));
#endif
                            }
#if PAL
                            Ghost<SortedSetLabels<T>> rotated = SortedSetLift.Rotated(sub.Value, sibling);
                            SortedSetEditProof.Change<T>(SortedSetLift.Rotated(sub.Value, sibling), rotated);
                            SortedSetEditProof.Facts(rotated);
                            SortedSetEditProof.OpenColor(rotated, parent);
#endif
                            parent.ColorRed();
#if PAL
                            SortedSetEditProof.CloseRed(rotated, parent);
                            Ghost<SortedSetLabels<T>> redParent = SortedSetEdit.Recolor(rotated.Value, parent, true);
                            SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(rotated.Value, parent, true), redParent);
                            SortedSetEditProof.Facts(redParent);
                            SortedSetOwnershipProof.RootFacts(redParent);
                            SortedSetEditProof.OpenColor(redParent, sibling);
#endif
                            sibling.ColorBlack(); // The red parent can't have black children.
#if PAL
                            SortedSetEditProof.CloseBlack(redParent, sibling);
                            SortedSetBalance.TopColor(redParent.Value, sibling, false);
                            Ghost<SortedSetLabels<T>> replacement = SortedSetLift.Lifted(sub.Value, sibling);
                            SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(redParent.Value, sibling, false), replacement);
#endif
                            // `sibling` becomes the child of `grandParent` or `root` after rotation. Update the link from that node.
                            ReplaceChildOrRoot(grandParent, parent, sibling);
                            // `sibling` will become the grandparent of `current`.
                            grandParent = sibling;
                            if (parent == match)
                            {
                                parentOfMatch = sibling;
                            }

#if PAL
                            Ghost<SortedSetLabels<T>> lifted = SortedSetOwnership.Active(ownershipState);
                            SortedSetRemove.AtMid(comparer, k0.Value, item, lifted.Value, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value);
                            SortedSetEditProof.BeginOwner(root, ownershipState);
                            SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), lifted);
                            SortedSetOwnershipProof.OpenRead(lifted, parent, Perm.Full);
#endif
                            sibling = parent.GetSibling(current);
#if PAL
                            SortedSetOwnershipProof.CloseRead(lifted, Perm.Full);
                            SortedSetEditProof.EndOwner(root, ownershipState, lifted);
                            ownershipState = SortedSetEdit.ReplaceState(ownershipState, lifted);
#endif
                        }
#if PAL
                        else
                        {
                            SortedSetOwnershipProof.CloseRead(before, Perm.Full);
                            SortedSetRemove.Direct(comparer, k0.Value, item, before.Value, current, parent, grandParent, match, parentOfMatch, foundMatch);
                            SortedSetEditProof.EndOwner(root, ownershipState, before);
                            ownershipState = SortedSetEdit.ReplaceState(ownershipState, before);
                        }
                        Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                        Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) && version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
                        Pal.Join(SortedSetRemove.Mid(comparer, k0.Value, item, SortedSetOwnership.Active(ownershipState), current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value));
                        Pal.Join(current != null && parent != null && sibling != null);
                        Pal.Join(sibling == SortedSetRemove.Sibling(SortedSetOwnership.Active(ownershipState), parent, current));
                        Ghost<SortedSetLabels<T>> middle = SortedSetOwnership.Active(ownershipState);
                        SortedSetRemove.AtMid(comparer, k0.Value, item, middle.Value, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value);
                        SortedSetEditProof.BeginOwner(root, ownershipState);
                        SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), middle);
                        SortedSetFrontierProof.OpenRead(middle, sibling);
                        SortedSetFrontier.Read2Facts(SortedSetEdit.Sub(middle.Value, sibling));
#endif
                        Debug.Assert(Node.IsNonNullBlack(sibling));
                        if (sibling.Is2Node)
                        {
#if PAL
                            SortedSetFrontierProof.CloseRead(middle, sibling);
                            SortedSetFrontierProof.OpenMerge(middle, parent);
#endif
                            parent.Merge2Nodes();
#if PAL
                            SortedSetFrontierProof.CloseMerge(middle, parent);
                            SortedSetRemove.Merge(comparer, k0.Value, item, middle.Value, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value);
                            Ghost<SortedSetLabels<T>> merged = SortedSetFrontier.Merged(middle.Value, parent);
                            SortedSetEditProof.Change<T>(SortedSetFrontier.Merged(middle.Value, parent), merged);
                            SortedSetEditProof.EndOwner(root, ownershipState, merged);
                            ownershipState = SortedSetEdit.ReplaceState(ownershipState, merged);
#endif
                        }
                        else
                        {
                            // `current` is a 2-node and `sibling` is either a 3-node or a 4-node.
                            // We can change the color of `current` to red by some rotation.
#if PAL
                            SortedSetFrontierProof.CloseRead(middle, sibling);
                            SortedSetRemove.Borrow(comparer, k0.Value, item, middle.Value, current, parent, grandParent, match, parentOfMatch, foundMatch, m0.Value);
                            SortedSetRemove.Selection(middle.Value, parent, current);
                            Ghost<SortedSetLabels<T>> sub = SortedSetEdit.Sub(middle.Value, parent);
                            Ghost<TreeRotation> rotation = SortedSetRemove.Rotation(middle.Value, parent, current);
                            Ghost<bool> direction = SortedSetLift.Right(sub.Value, sibling);
                            SortedSetEditProof.Cut(middle, parent);
                            SortedSetEditProof.Change<T>(SortedSetEdit.Sub(middle.Value, parent), sub);
                            SortedSetEditProof.Facts(sub);
                            SortedSetDispatchProof.OpenSelector(parent, sibling, sub, direction);
#endif
                            Node newGrandParent = parent.Rotate(parent.GetRotation(current, sibling))!;
                            newGrandParent.Color = parent.Color;
#if PAL
                            SortedSetDispatchProof.CloseRed(parent, newGrandParent, sub, rotation.Value);
                            Ghost<SortedSetLabels<T>> colored = SortedSetDispatch.Colored(sub.Value, rotation.Value);
                            SortedSetEditProof.Change<T>(SortedSetDispatch.Colored(sub.Value, rotation.Value), colored);
                            SortedSetEditProof.Facts(colored);
                            SortedSetEditProof.OpenColor(colored, parent);
#endif
                            parent.ColorBlack();
#if PAL
                            SortedSetEditProof.CloseBlack(colored, parent);
                            SortedSetBalance.TopColor(colored.Value, parent, false);
                            Ghost<SortedSetLabels<T>> blackened = SortedSetDispatch.Blackened(sub.Value, rotation.Value);
                            SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(colored.Value, parent, false), blackened);
                            SortedSetEditProof.Facts(blackened);
                            SortedSetEditProof.OpenColor(blackened, current);
#endif
                            current.ColorRed();
#if PAL
                            SortedSetEditProof.CloseRed(blackened, current);
                            SortedSetBalance.TopColor(blackened.Value, current, true);
                            Ghost<SortedSetLabels<T>> replacement = SortedSetDispatch.Borrowed(sub.Value, current, rotation.Value);
                            SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(blackened.Value, current, true), replacement);
#endif
                            ReplaceChildOrRoot(grandParent, parent, newGrandParent);
                            if (parent == match)
                            {
                                parentOfMatch = newGrandParent;
                            }
                        }
                    }
                }
#if PAL
                else
                {
                    SortedSetFrontierProof.CloseRead(before, current);
                    SortedSetRemove.Not2(comparer, k0.Value, item, before.Value, current, parent, grandParent, match, parentOfMatch, foundMatch);
                    SortedSetEditProof.EndOwner(root, ownershipState, before);
                    ownershipState = SortedSetEdit.ReplaceState(ownershipState, before);
                }
                Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                Pal.Join(comparer == Pal.Old(this.SpecComparer) && count == Pal.Old(this.SpecCount) && version == SpecWrap.Int32(Pal.Old(this.SpecVersion) + 1));
                Pal.Join(current != null);
                Pal.Join(SortedSetRemove.Fixed(comparer, k0.Value, item, SortedSetOwnership.Active(ownershipState), current, parent, match, parentOfMatch, foundMatch, m0.Value));
                Ghost<SortedSetLabels<T>> fixedTree = SortedSetOwnership.Active(ownershipState);
                SortedSetRemove.AtFixed(comparer, k0.Value, item, fixedTree.Value, current, parent, match, parentOfMatch, foundMatch, m0.Value);
                SortedSetEditProof.BeginOwner(root, ownershipState);
                SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), fixedTree);
                SortedSetOwnershipProof.OpenRead(fixedTree, current, Perm.Full);
#endif
                // We don't need to compare after we find the match.
                int order = foundMatch ? -1 : comparer.Compare(item, current.Item);
#if PAL
                SortedSetOwnershipProof.CloseRead(fixedTree, Perm.Full);
                SortedSetRemove.Advance(comparer, k0.Value, item, fixedTree.Value, current, parent, match, parentOfMatch, foundMatch, m0.Value, order);
#endif
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
#if PAL
                SortedSetOwnershipProof.OpenRead(fixedTree, current, Perm.Full);
#endif
                current = order < 0 ? current.Left : current.Right;
#if PAL
                SortedSetOwnershipProof.CloseRead(fixedTree, Perm.Full);
                SortedSetEditProof.EndOwner(root, ownershipState, fixedTree);
                ownershipState = SortedSetEdit.ReplaceState(ownershipState, fixedTree);
                progress = ownershipState;
#endif
            }
#if PAL
            Ghost<SortedSetLabels<T>> searched = SortedSetOwnership.Active(ownershipState);
            SortedSetRemove.End(comparer, k0.Value, item, searched.Value, parent, grandParent, match, parentOfMatch, foundMatch);
            SortedSetRemove.Cardinality(comparer, k0.Value, item);
            Ghost<Seq<T>> k1 = SpecTopDownRemove.Removed(comparer, k0.Value, item);
#endif
            // Move successor to the matching node position and replace links.
            if (match != null)
            {
                ReplaceNode(match, parentOfMatch!, parent!, grandParent!);
                --count;
            }
#if PAL
            Ghost<SortedSetLabels<T>> finalTree = SortedSetOwnership.Active(ownershipState);
            SortedSetRemove.Finish(comparer, k0.Value, item, finalTree.Value);
            SortedSetEditProof.BeginOwner(root, ownershipState);
            SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), finalTree);
            SortedSetOwnershipProof.RootFacts(finalTree);
#endif
            Node? rootForColor = root;
            if (rootForColor != null)
            {
#if PAL
                SortedSetEditProof.OpenColor(finalTree, rootForColor);
#endif
                rootForColor.ColorBlack();
#if PAL
                SortedSetEditProof.CloseBlack(finalTree, rootForColor);
                SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(finalTree.Value, rootForColor, false),
                    SortedSetLocal.Color(finalTree.Value, false));
#endif
            }
#if PAL
            else
            {
                SortedSetEditProof.Change<T>(finalTree, SortedSetLocal.Color(finalTree.Value, false));
            }
            Ghost<SortedSetLabels<T>> done = SortedSetLocal.Color(finalTree.Value, false);
            SortedSetEditProof.Change<T>(SortedSetLocal.Color(finalTree.Value, false), done);
            SortedSetEditProof.EndOwner(root, ownershipState, done);
            ownershipState = SortedSetEdit.ReplaceState(ownershipState, done);
#endif
            return foundMatch;
        }

        [Ensures("@this.SpecItems.Length == 0")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public virtual void Clear()
        {
#if PAL
            SortedSetOwnershipProof.RetainClear(root, ownershipState);
            ownershipState = SortedSetOwnership.Cleared(ownershipState);
#endif
            root = null;
            count = 0;
            ++version;
        }

        [Ensures("Result == (Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Requires("@this.SpecCoherent", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Result == (SpecSearchTree.InRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item) && Pal.KeyIndex(@this._underlying.SpecComparer, @this._underlying.SpecItems, item) >= 0)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("@this.SpecCoherent", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
        [Frac("p")]
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
        [Ensures("SortedSetState.Walkable(@this.SpecObservation, Result._stack.Items)")]
        [Ensures("SortedSetState.Pending(false, @this.SpecObservation, Result._stack.Items) == @this.SpecItems")]
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
        [Requires("SortedSetOwnership.Owner(@this.root, @this.ownershipState, Perm.Full)")]
        [Requires("SortedSetBalance.Ready(SortedSetOwnership.Active(@this.ownershipState), current, parent, grandParent, greatGrandParent)")]
        [Ensures("SortedSetOwnership.Owner(@this.root, @this.ownershipState, Perm.Full)")]
        [Ensures("Pal.Same(SortedSetOwnership.Active(@this.ownershipState), SortedSetBalance.Balanced(SortedSetOwnership.Active(Pal.Old(@this.ownershipState)), current))")]
        [Ensures("parent == (SortedSetBalance.SameSide(SortedSetOwnership.Active(Pal.Old(@this.ownershipState)), current) ? Pal.Old(parent) : greatGrandParent)")]
        [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
        private void InsertionBalance(Node current, ref Node parent, Node grandParent, [System.Diagnostics.CodeAnalysis.AllowNull] Node greatGrandParent)
        {
            Debug.Assert(parent != null);
            Debug.Assert(grandParent != null);

#if PAL
            Ghost<SortedSetLabels<T>> before = SortedSetOwnership.Active(ownershipState);
            Ghost<Node> parent0 = parent;
            SortedSetEditProof.BeginOwner(root, ownershipState);
            SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), before);
            SortedSetBalance.Layout(before.Value, current, parent, grandParent, greatGrandParent);
            SortedSetOwnershipProof.OpenRead(before, grandParent, Perm.Full);
#endif
            bool parentIsOnRight = grandParent.Right == parent;
#if PAL
            SortedSetOwnershipProof.CloseRead(before, Perm.Full);
            SortedSetOwnershipProof.OpenRead(before, parent, Perm.Full);
#endif
            bool currentIsOnRight = parent.Right == current;
#if PAL
            SortedSetOwnershipProof.CloseRead(before, Perm.Full);
            Ghost<SortedSetLabels<T>> sub = SortedSetEdit.Sub(before.Value, grandParent);
            Ghost<SortedSetLabels<T>> rotated = SortedSetBalance.Rotated(currentIsOnRight, parentIsOnRight, sub.Value);
            SortedSetEditProof.Cut(before, grandParent);
            SortedSetEditProof.Change<T>(SortedSetEdit.Sub(before.Value, grandParent), sub);
#endif

            Node newChildOfGreatGrandParent;
            if (parentIsOnRight == currentIsOnRight)
            {
                // Same orientation, single rotation
#if PAL
                SortedSetBalanceProof.OpenSingle(grandParent, sub, currentIsOnRight);
#endif
                newChildOfGreatGrandParent = currentIsOnRight ? grandParent.RotateLeft() : grandParent.RotateRight();
#if PAL
                SortedSetBalanceProof.CloseSingle(grandParent, newChildOfGreatGrandParent, sub, currentIsOnRight);
                SortedSetEditProof.Change<T>(SortedSetBalance.Single(sub.Value, currentIsOnRight), rotated);
#endif
            }
            else
            {
                // Different orientation, double rotation
#if PAL
                SortedSetBalanceProof.OpenDouble(grandParent, sub, currentIsOnRight);
#endif
                newChildOfGreatGrandParent = currentIsOnRight ? grandParent.RotateLeftRight() : grandParent.RotateRightLeft();
#if PAL
                SortedSetBalanceProof.CloseDouble(grandParent, newChildOfGreatGrandParent, sub, currentIsOnRight);
                SortedSetEditProof.Change<T>(SortedSetBalance.Double(sub.Value, currentIsOnRight), rotated);
#endif
                // Current node now becomes the child of `greatGrandParent`
                parent = greatGrandParent!;
            }

#if PAL
            Pal.Join(SortedSetOwnership.Owns(rotated.Value, Perm.Full));
            Pal.Join(SortedSetEdit.Pending(before.Value, grandParent));
            Pal.Join(SortedSetEdit.Retained(ownershipState));
            Pal.Join(newChildOfGreatGrandParent == SortedSetOwnership.Top(rotated.Value));
            Pal.Join(parent == (SortedSetBalance.SameSide(before.Value, current) ? parent0.Value : greatGrandParent));
            SortedSetEditProof.Facts(rotated);
            SortedSetBalance.RotatedFacts(sub.Value, currentIsOnRight, parentIsOnRight);
            SortedSetBalance.TopColor(rotated.Value, grandParent, true);
            Ghost<SortedSetLabels<T>> redModel = SortedSetEdit.Recolor(rotated.Value, grandParent, true);
            SortedSetEditProof.OpenColor(rotated, grandParent);
#endif

            // `grandParent` will become a child of either `parent` of `current`.
            grandParent.ColorRed();
#if PAL
            SortedSetEditProof.CloseRed(rotated, grandParent);
            SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(rotated.Value, grandParent, true), redModel);
            SortedSetEditProof.Facts(redModel);
            SortedSetOwnershipProof.RootFacts(redModel);
            SortedSetEditProof.OpenColor(redModel, newChildOfGreatGrandParent);
#endif
            newChildOfGreatGrandParent.ColorBlack();
#if PAL
            SortedSetEditProof.CloseBlack(redModel, newChildOfGreatGrandParent);
            SortedSetBalance.Result(sub.Value, currentIsOnRight, parentIsOnRight);
            Ghost<SortedSetLabels<T>> replacement = SortedSetBalance.SubBalanced(currentIsOnRight, parentIsOnRight, sub.Value);
            SortedSetEditProof.Change<T>(SortedSetEdit.Recolor(redModel.Value, newChildOfGreatGrandParent, false), replacement);
#endif
            ReplaceChildOrRoot(greatGrandParent, grandParent, newChildOfGreatGrandParent);
        }

        /// <summary>
        /// Replaces the child of a parent node, or replaces the root if the parent is <c>null</c>.
        /// </summary>
        /// <param name="parent">The (possibly <c>null</c>) parent.</param>
        /// <param name="child">The child node to replace.</param>
        /// <param name="newChild">The node to replace <paramref name="child"/> with.</param>
        [Open]
        [Requires("SortedSetOwnership.Good(labels) && SortedSetOwnership.Member(labels, child)")]
        [Requires("parent == SortedSetEdit.Parent(labels, child)")]
        [Requires("Pal.Same(SortedSetOwnership.Active(@this.ownershipState), labels) && @this.root == SortedSetOwnership.Top(labels)")]
        [Requires("newChild == SortedSetOwnership.Top(replacement)")]
        [Requires("SortedSetEdit.Pending(labels, child)")]
        [Requires("SortedSetOwnership.Owns(replacement, Perm.Full)")]
        [Requires("SortedSetEdit.Retained(@this.ownershipState)")]
        [Ensures("SortedSetOwnership.Owner(@this.root, @this.ownershipState, Perm.Full)")]
        [Ensures("Pal.Same(SortedSetOwnership.Active(@this.ownershipState), SortedSetEdit.Replace(labels, child, replacement))")]
        [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
        private void ReplaceChildOrRoot(Node? parent, Node child, [System.Diagnostics.CodeAnalysis.AllowNull] Node newChild
#if PAL
            , Ghost<SortedSetLabels<T>> labels = default, Ghost<SortedSetLabels<T>> replacement = default
#endif
            )
        {
            if (parent != null)
            {
#if PAL
                SortedSetEditProof.OpenParent(labels, child, parent);
#endif
                parent.ReplaceChild(child, newChild);
#if PAL
                SortedSetEditProof.CloseParent(labels, child, parent, replacement);
#endif
            }
            else
            {
                root = newChild;
#if PAL
                SortedSetEditProof.CloseRoot(labels, child, replacement);
#endif
            }
#if PAL
            Ghost<SortedSetLabels<T>> updated = SortedSetEdit.Replace(labels.Value, child, replacement.Value);
            SortedSetEditProof.Change<T>(SortedSetEdit.Replace(labels.Value, child, replacement.Value), updated);
            SortedSetEditProof.EndOwner(root, ownershipState, updated);
            ownershipState = SortedSetEdit.ReplaceState(ownershipState, updated);
#endif
        }

        /// <summary>
        /// Replaces the matching node with its successor.
        /// </summary>
        [Open]
        [Requires("SortedSetOwnership.Owner(@this.root, @this.ownershipState, Perm.Full)")]
        [Requires("SortedSetOwnership.Good(SortedSetOwnership.Active(@this.ownershipState)) && SortedSetOwnership.Member(SortedSetOwnership.Active(@this.ownershipState), match)")]
        [Requires("parentOfMatch == SortedSetEdit.Parent(SortedSetOwnership.Active(@this.ownershipState), match)")]
        [Requires("successor == SortedSetSuccessor.Successor(SortedSetEdit.Sub(SortedSetOwnership.Active(@this.ownershipState), match))")]
        [Requires("Pal.Implies(SortedSetLocal.Branch(SortedSetLocal.Right(SortedSetEdit.Sub(SortedSetOwnership.Active(@this.ownershipState), match))), parentOfSuccessor == SortedSetSuccessor.ParentOfSuccessor(SortedSetEdit.Sub(SortedSetOwnership.Active(@this.ownershipState), match)))")]
        [Ensures("SortedSetOwnership.Owner(@this.root, @this.ownershipState, Perm.Full)")]
        [Ensures("Pal.Same(SortedSetOwnership.Active(@this.ownershipState), SortedSetSuccessor.Delete(SortedSetOwnership.Active(Pal.Old(@this.ownershipState)), match))")]
        [Ensures("@this.comparer == Pal.Old(@this.comparer) && @this.count == Pal.Old(@this.count) && @this.version == Pal.Old(@this.version)")]
        private void ReplaceNode(Node match, [System.Diagnostics.CodeAnalysis.AllowNull] Node parentOfMatch, Node successor, [System.Diagnostics.CodeAnalysis.AllowNull] Node parentOfSuccessor)
        {
            Debug.Assert(match != null);

#if PAL
            Ghost<SortedSetLabels<T>> labels = SortedSetOwnership.Active(ownershipState);
            SortedSetEditProof.BeginOwner(root, ownershipState);
            SortedSetEditProof.Change<T>(SortedSetOwnership.Active(ownershipState), labels);
            SortedSetEditProof.Cut(labels, match);
            Ghost<SortedSetLabels<T>> removed = SortedSetEdit.Sub(labels.Value, match);
            SortedSetEditProof.Change<T>(SortedSetEdit.Sub(labels.Value, match), removed);
            SortedSetEditProof.Facts(removed);
            SortedSetOwnershipProof.RootFacts(removed);
            SortedSetSuccessorProof.Layout(successor, parentOfSuccessor, removed);
            Ghost<SortedSetNodeSnapshot<T>> originalCell = SortedSetSuccessor.Snapshot(removed.Value);
            SortedSetLocalProof.Open(match, removed);
#endif
            if (successor == match)
            {
                // This node has no successor. This can only happen if the right child of the match is null.
                Debug.Assert(match.Right == null);
                successor = match.Left!;
#if PAL
                SortedSetSuccessorProof.NoRight(removed);
#endif
            }
            else
            {
                Debug.Assert(parentOfSuccessor != null);
                Debug.Assert(successor.Left == null);
                Debug.Assert((successor.Right == null && successor.IsRed) || (successor.Right!.IsRed && successor.IsBlack));

#if PAL
                Ghost<SortedSetLabels<T>> rightModel = SortedSetLocal.Right(removed.Value);
                Ghost<SortedSetLabels<T>> minimum = SortedSetEdit.Sub(rightModel.Value, successor);
                SortedSetEditProof.Change<T>(SortedSetLocal.Right(removed.Value), rightModel);
                SortedSetEditProof.Cut(rightModel, successor);
                SortedSetEditProof.Change<T>(SortedSetEdit.Sub(rightModel.Value, successor), minimum);
                SortedSetLocalProof.Open(successor, minimum);
                SortedSetSuccessorProof.Empty<T>(SortedSetLocal.Left(minimum.Value));
                SortedSetEditProof.Facts<T>(SortedSetLocal.Right(minimum.Value));
                SortedSetOwnershipProof.RootFacts<T>(SortedSetLocal.Right(minimum.Value));
#endif
                Node? rightForColor = successor.Right;
                if (rightForColor != null)
                {
#if PAL
                    SortedSetLocalProof.Open<T>(rightForColor, SortedSetLocal.Right(minimum.Value));
#endif
                    rightForColor.ColorBlack();
#if PAL
                    SortedSetLocalProof.BlackLeaves<T>(SortedSetLocal.Right(minimum.Value));
                    SortedSetLocalProof.Close<T>(rightForColor, SortedSetLocal.Color(SortedSetLocal.Right(minimum.Value), false));
#endif
                }
#if PAL
                else
                {
                    SortedSetEditProof.Change<T>(SortedSetLocal.Right(minimum.Value),
                        SortedSetLocal.Color(SortedSetLocal.Right(minimum.Value), false));
                }
#endif

                if (parentOfSuccessor != match)
                {
                    // Detach the successor from its parent and set its right child.
#if PAL
                    SortedSetEditProof.OpenParent(rightModel, successor, parentOfSuccessor);
#endif
                    parentOfSuccessor.Left = successor.Right;
#if PAL
                    SortedSetEditProof.CloseParent<T>(rightModel, successor, parentOfSuccessor,
                        SortedSetLocal.Color(SortedSetLocal.Right(minimum.Value), false));
#endif
                    successor.Right = match.Right;
                }
#if PAL
                else
                {
                    SortedSetEditProof.CloseRoot<T>(rightModel, successor,
                        SortedSetLocal.Color(SortedSetLocal.Right(minimum.Value), false));
                }
                SortedSetEditProof.Change<T>(
                    SortedSetEdit.Replace(rightModel.Value, successor, SortedSetLocal.Color(SortedSetLocal.Right(minimum.Value), false)),
                    SortedSetSuccessor.Remaining(removed.Value));
#endif
                successor.Left = match.Left;
#if PAL
                SortedSetSuccessorProof.Leaves(removed);
                SortedSetLocalProof.Close<T>(successor, SortedSetSuccessor.PreColor(removed.Value));
#endif
            }
#if PAL
            Pal.Join(SortedSetOwnership.Owns(SortedSetSuccessor.PreColor(removed.Value), Perm.Full));
            Pal.Join(SortedSetSuccessor.Cell(match, removed.Value));
            Pal.Join(SortedSetEdit.Pending(labels.Value, match));
            Pal.Join(SortedSetEdit.Retained(ownershipState));
            Pal.Join(successor == SortedSetOwnership.Top(SortedSetSuccessor.PreColor(removed.Value)));
#endif
            if (successor != null)
            {
#if PAL
                SortedSetLocalProof.Open<T>(successor, SortedSetSuccessor.PreColor(removed.Value));
#endif
                successor.Color = match.Color;
#if PAL
                SortedSetLocalProof.ColorLeaves<T>(SortedSetSuccessor.PreColor(removed.Value), SortedSetLocal.Red(removed.Value));
                SortedSetLocalProof.Close<T>(successor, SortedSetSuccessor.Replacement(removed.Value));
#endif
            }
#if PAL
            else
            {
                SortedSetEditProof.Change<T>(SortedSetSuccessor.PreColor(removed.Value),
                    SortedSetSuccessor.Replacement(removed.Value));
            }
            Ghost<SortedSetLabels<T>> replacement = SortedSetSuccessor.Replacement(removed.Value);
            SortedSetEditProof.Change<T>(SortedSetSuccessor.Replacement(removed.Value), replacement);
            SortedSetSuccessorProof.Canonical(match, removed, originalCell);
#endif
            ReplaceChildOrRoot(parentOfMatch, match, successor!);
#if PAL
            SortedSetOwnershipProof.RetainCell(root, match, ownershipState, originalCell);
            ownershipState = SortedSetOwnership.RetiredCell(ownershipState, match, originalCell);
#endif
        }

        [Ensures("(Result != null) == (Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0)")]
        [Ensures("Result == null || SortedSetOwnership.Member(@this.SpecLabels, Result) && Pal.Same(SpecSearchTree.RootKey(SortedSetOwnership.Lookup(@this.SpecLabels, Result), item), SpecSearchTree.Find(@this.SpecComparer, @this.SpecNodes, item, item))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Requires("@this.root == null || SortedSetOwnership.Member(@this._underlying.SpecLabels, @this.root)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("(Result != null) == SpecSearchTree.Contains(@this.comparer, SortedSetOwnership.Lookup(@this._underlying.SpecLabels, @this.root), item)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Result == null || SortedSetOwnership.Member(@this._underlying.SpecLabels, Result) && Pal.Same(SpecSearchTree.RootKey(SortedSetOwnership.Lookup(@this._underlying.SpecLabels, Result), item), SpecSearchTree.Find(@this.comparer, SortedSetOwnership.Lookup(@this._underlying.SpecLabels, @this.root), item, item))", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("@this.root == Pal.Old(@this.root) && @this.comparer == Pal.Old(@this.comparer)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
        [Frac("p")]
        internal virtual Node? FindNode(T item)
        {
#if PAL
            Ghost<SortedSetLabels<T>> labels = this is TreeSubSet view ? view.ReadLabels : this.SpecLabels;
            SortedSetOwnershipProof.RootFacts(labels);
            Ghost<SpecTree<(T, bool)>> searched = SortedSetOwnership.Lookup(labels.Value, root);
            if (this is TreeSubSet)
                SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
            else
                SortedSetOwnershipProof.ReadOwner(root, ownershipState, labels, Pal.Permission());
#endif
            Node? current = root;
            while (current != null)
            {
#if PAL
                Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                Pal.Invariant(SortedSetOwnership.Owns(labels.Value, Pal.Permission()));
                Pal.Invariant(Pal.Implies(!Pal.Returned(),
                              SpecSearchTree.Contains(comparer, SortedSetOwnership.Lookup(labels.Value, current), item) ==
                              SpecSearchTree.Contains(comparer, searched.Value, item) &&
                              (current == null || SortedSetOwnership.Member(labels.Value, current)) &&
                              Pal.Same(SpecSearchTree.Find(comparer, SortedSetOwnership.Lookup(labels.Value, current), item, item),
                                       SpecSearchTree.Find(comparer, searched.Value, item, item))));
                Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.ReturnValue<Node?>() != null &&
                              SpecSearchTree.Contains(comparer, searched.Value, item) &&
                              SortedSetOwnership.Member(labels.Value, Pal.ReturnValue<Node?>()) &&
                              Pal.Same(SpecSearchTree.RootKey(SortedSetOwnership.Lookup(labels.Value, Pal.ReturnValue<Node?>()), item),
                                       SpecSearchTree.Find(comparer, searched.Value, item, item))));
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
#endif
                int order = comparer.Compare(item, current.Item);
#if PAL
                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
                if (order == 0)
                {
                    return current;
                }

#if PAL
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
#endif
                current = order < 0 ? current.Left : current.Right;
#if PAL
                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
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
        [Fuel(1, 0)]
        [Requires("@this.SpecNodes.Height <= 30")]
        [Ensures("Result == SpecSearchTree.HeapIndex(@this.SpecComparer, @this.SpecNodes, item, 0)")]
        [Ensures("(Result >= 0) == (Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0)")]
        [Ensures("Result <= SpecSearchTree.Breadth(@this.SpecNodes) - 2")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Requires("(@this.root == null || SortedSetOwnership.Member(@this._underlying.SpecLabels, @this.root)) && SortedSetOwnership.Lookup(@this._underlying.SpecLabels, @this.root).Height <= 30", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Result == SpecSearchTree.HeapIndex(@this.comparer, SortedSetOwnership.Lookup(@this._underlying.SpecLabels, @this.root), item, 0)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("@this.root == Pal.Old(@this.root) && @this.comparer == Pal.Old(@this.comparer)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
        [Frac("p")]
        internal int InternalIndexOf(T item)
        {
#if PAL
            Ghost<SortedSetLabels<T>> labels = this is TreeSubSet view ? view.ReadLabels : this.SpecLabels;
            SortedSetOwnershipProof.RootFacts(labels);
            Ghost<SpecTree<(T, bool)>> searched = SortedSetOwnership.Lookup(labels.Value, root);
            if (this is TreeSubSet)
                SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
            else
                SortedSetOwnershipProof.ReadOwner(root, ownershipState, labels, Pal.Permission());
#endif
            Node? current = root;
            int count = 0;
            while (current != null)
            {
#if PAL
                Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                Pal.Invariant(SortedSetOwnership.Owns(labels.Value, Pal.Permission()));
                Pal.Invariant(Pal.Implies(!Pal.Returned(), (current == null || SortedSetOwnership.Member(labels.Value, current)) &&
                              SpecSearchTree.IndexRoom(count, SortedSetOwnership.Lookup(labels.Value, current), searched.Value.Height) &&
                              SpecSearchTree.HeapIndex(comparer, SortedSetOwnership.Lookup(labels.Value, current), item, count) ==
                              SpecSearchTree.HeapIndex(comparer, searched.Value, item, 0)));
                Pal.Invariant(Pal.Implies(Pal.Returned(),
                              Pal.ReturnValue<int>() == SpecSearchTree.HeapIndex(comparer, searched.Value, item, 0)));
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                SortedSetOwnershipProof.IndexBounds<T>(count, SortedSetOwnership.Lookup(labels.Value, current), searched.Value.Height);
#endif
                int order = comparer.Compare(item, current.Item);
#if PAL
                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
                if (order == 0)
                {
                    return count;
                }

#if PAL
                SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
#endif
                current = order < 0 ? current.Left : current.Right;
#if PAL
                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
#endif
                count = order < 0 ? (2 * count + 1) : (2 * count + 2);
            }

            return -1;
        }

        [Ensures("(Result != null) == SpecSearchTree.AnyInRange(@this.SpecComparer, @this.SpecItems, from, to, true, true)")]
        [Ensures("Result == null || SortedSetOwnership.Member(@this.SpecLabels, Result) && SpecSearchTree.InRange(@this.SpecComparer, from, to, true, true, SpecSearchTree.RootKey(SortedSetOwnership.Lookup(@this.SpecLabels, Result), from))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        internal Node? FindRange(T? from, T? to) => FindRange(from, to, lowerBoundActive: true, upperBoundActive: true, level: out _);

        [Ensures("(Result != null) == SpecSearchTree.AnyInRange(@this.SpecComparer, @this.SpecItems, from, to, lowerBoundActive, upperBoundActive)")]
        [Ensures("Result == null || SortedSetOwnership.Member(@this.SpecLabels, Result) && SpecSearchTree.InRange(@this.SpecComparer, from, to, lowerBoundActive, upperBoundActive, SpecSearchTree.RootKey(SortedSetOwnership.Lookup(@this.SpecLabels, Result), from))")]
        [Ensures("SortedSetOwnership.Lookup(@this.SpecLabels, Result) == SpecSearchTree.RangeRoot(@this.SpecComparer, @this.SpecNodes, from, to, lowerBoundActive, upperBoundActive)")]
        [Ensures("level == SortedSetCount.RangeDepth(@this.SpecComparer, @this.SpecNodes, from, to, lowerBoundActive, upperBoundActive)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Frac("p")]
        [Rlimit(4)]
        [Fuel(4, 2)]
        internal Node? FindRange(T? from, T? to, bool lowerBoundActive, bool upperBoundActive, out int level)
        {
#if PAL
            Ghost<SortedSetLabels<T>> labels = SortedSetOwnership.Active(ownershipState);
            Ghost<SortedSetSnapshot<T>> snapshot = SortedSetOwnership.Snapshot(this.SpecSnapshot);
            SortedSetOwnershipProof.RootFacts(labels);
#endif
            Node? current = root;
            level = 0;
#if PAL
            SortedSetCount.RangeDepthLeSize(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive);
#endif
            while (current != null)
            {
#if PAL
                Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                Pal.Invariant(SortedSetOwnership.Owner(root, ownershipState, Pal.Permission()));
                Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, snapshot.Value));
                Pal.Invariant(Pal.Implies(!Pal.Returned(),
                              0 <= level && level + SortedSetCount.RangeDepth(comparer, SortedSetOwnership.Lookup(labels.Value, current), from, to, lowerBoundActive, upperBoundActive) ==
                              SortedSetCount.RangeDepth(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive)));
                Pal.Invariant(Pal.Implies(Pal.Returned(),
                              level == SortedSetCount.RangeDepth(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive)));
                Pal.Invariant(Pal.Implies(!Pal.Returned(), (current == null || SortedSetOwnership.Member(labels.Value, current)) &&
                              SpecSearchTree.RangeHit(comparer, SortedSetOwnership.Lookup(labels.Value, current), from, to, lowerBoundActive, upperBoundActive) ==
                              SpecSearchTree.RangeHit(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive) &&
                              SpecSearchTree.RangeRoot(comparer, SortedSetOwnership.Lookup(labels.Value, current), from, to, lowerBoundActive, upperBoundActive) ==
                              SpecSearchTree.RangeRoot(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive)));
                Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.ReturnValue<Node?>() != null &&
                              SortedSetOwnership.Lookup(labels.Value, Pal.ReturnValue<Node?>()) ==
                              SpecSearchTree.RangeRoot(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive) &&
                              SpecSearchTree.RangeHit(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive) &&
                              SortedSetOwnership.Member(labels.Value, Pal.ReturnValue<Node?>()) &&
                              SpecSearchTree.InRange(comparer, from, to, lowerBoundActive, upperBoundActive,
                                                     SpecSearchTree.RootKey(SortedSetOwnership.Lookup(labels.Value, Pal.ReturnValue<Node?>()), from))));
                Ghost<SpecInt> beforeSize = SortedSetOwnership.Lookup(labels.Value, current).Size;
                SortedSetOwnershipProof.OpenNode(root, ownershipState, current, Pal.Permission());
#endif
                if (lowerBoundActive && comparer.Compare(from, current.Item) > 0)
                {
                    current = current.Right;
#if PAL
                    SortedSetOwnershipProof.CloseNode(root, ownershipState, Pal.Permission());
#endif
                }
                else
                {
                    if (upperBoundActive && comparer.Compare(to, current.Item) < 0)
                    {
                        current = current.Left;
#if PAL
                        SortedSetOwnershipProof.CloseNode(root, ownershipState, Pal.Permission());
#endif
                    }
                    else
                    {
#if PAL
                        SortedSetOwnershipProof.CloseNode(root, ownershipState, Pal.Permission());
#endif
                        return current;
                    }
                }
#if PAL
                Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Pal.Permission()));
                Pal.Join(Pal.Implies(!Pal.Returned(),
                    0 <= level &&
                    level + 1 + SortedSetCount.RangeDepth(comparer, SortedSetOwnership.Lookup(labels.Value, current), from, to, lowerBoundActive, upperBoundActive) ==
                    SortedSetCount.RangeDepth(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive) &&
                    SortedSetOwnership.Lookup(labels.Value, current).Size < beforeSize.Value &&
                    (current == null || SortedSetOwnership.Member(labels.Value, current)) &&
                    SpecSearchTree.RangeHit(comparer, SortedSetOwnership.Lookup(labels.Value, current), from, to, lowerBoundActive, upperBoundActive) ==
                    SpecSearchTree.RangeHit(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive) &&
                    SpecSearchTree.RangeRoot(comparer, SortedSetOwnership.Lookup(labels.Value, current), from, to, lowerBoundActive, upperBoundActive) ==
                    SpecSearchTree.RangeRoot(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive)));
                Pal.Join(Pal.Implies(Pal.Returned(),
                    level == SortedSetCount.RangeDepth(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive) &&
                    Pal.ReturnValue<Node?>() != null &&
                    SortedSetOwnership.Lookup(labels.Value, Pal.ReturnValue<Node?>()) ==
                    SpecSearchTree.RangeRoot(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive) &&
                    SpecSearchTree.RangeHit(comparer, SortedSetOwnership.Values(labels.Value), from, to, lowerBoundActive, upperBoundActive) &&
                    SortedSetOwnership.Member(labels.Value, Pal.ReturnValue<Node?>()) &&
                    SpecSearchTree.InRange(comparer, from, to, lowerBoundActive, upperBoundActive,
                        SpecSearchTree.RootKey(SortedSetOwnership.Lookup(labels.Value, Pal.ReturnValue<Node?>()), from))));
#endif
                level++;
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
        [Ensures("Pal.Implies(@this.SpecComparer == other.SpecComparer, Result)")]
        [Ensures("Result == (@this.SpecComparer == other.SpecComparer || SpecSortDedupe.ComparerEquals(@this.SpecComparer, other.SpecComparer))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("other.SpecNodes == Pal.Old(other.SpecNodes)")]
        [Ensures("other.SpecComparer == Pal.Old(other.SpecComparer)")]
        [Frac("p")]
        private bool HasEqualComparer(SortedSet<T> other)
        {
            // Commonly, both comparers will be the default comparer (and reference-equal). Avoid a virtual method call to Equals() in that case.
            return Comparer == other.Comparer || Comparer.Equals(other.Comparer);
        }

        #endregion

        #region ISet members

        // Which of two elements that compare equal stays depends on the branch: the merge keeps
        // `other`'s, `AddAllElements` this set's (doc/translation.md R27.55). Both are looked up
        // under this set's comparer, so the contract requires the same comparer (R27.47); the
        // merge's array and ConstructRootFromSortedArray's midpoint bound the sizes.
        [Requires("@this.SpecComparer == other.SpecComparer")]
        [Requires("@this.SpecItems.Length + other.SpecItems.Length <= 1073741824")]
        [Ensures("@this.SpecItems == (Pal.Old(@this.SpecItems).Length == 0 || Pal.Old(other.SpecItems).Length > Pal.Old(@this.SpecItems).Length / 2 " +
                 "? SpecSetOps.Union(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), Pal.Old(other.SpecItems)) " +
                 ": SpecSetOps.AddAll(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), Pal.Old(other.SpecItems)))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer) && other.SpecItems == Pal.Old(other.SpecItems) && other.SpecComparer == Pal.Old(other.SpecComparer)")]
        [Rlimit(30)]
        [Fuel(0, 0)]
        public void UnionWith([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);
#if PAL
            Ghost<SortedSetSnapshot<T>> originalSnapshot = SortedSetOwnership.Snapshot(this.SpecSnapshot);
#endif

            SortedSet<T>? asSorted = other as SortedSet<T>;
            TreeSubSet? treeSubset = this as TreeSubSet;

            if (treeSubset != null)
            {
                // The contract makes `this` a SortedSet<T> itself (R27.1), not a view.
                Pal.Unreachable();
                VersionCheck();
            }

            if (asSorted != null && treeSubset == null && Count == 0)
            {
                SpecSetOps.UnionLeftEmpty(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                SortedSet<T> dummy = new SortedSet<T>(asSorted, comparer);
                root = dummy.root;
                count = dummy.count;
#if PAL
                Ghost<SortedSetRetainedPayload<T>> transferred =
                    SortedSetRetainedHolderProof.Transfer(root, ownershipState, dummy);
                ownershipState = SortedSetRetainedHolder.State(transferred.Value);
#endif
                version++;
                return;
            }

            // This actually hurts if N is much greater than M. The / 2 is arbitrary.
            if (asSorted != null && treeSubset == null && HasEqualComparer(asSorted) && (asSorted.Count > this.Count / 2))
            {
                Pal.Assert(asSorted.SpecItems.Length > this.SpecItems.Length / 2);
                // First do a merge sort to an array.
                T[] merged = new T[asSorted.Count + this.Count];
                Pal.Assert(merged.Length == this.SpecItems.Length + asSorted.SpecItems.Length);
                int c = 0;
                Enumerator mine = this.GetEnumerator();
                Enumerator theirs = asSorted.GetEnumerator();
                SortedSetMerge.Whole(this.SpecItems);
                SortedSetMerge.Whole(asSorted.SpecItems);
                SortedSetMerge.PendingNext(this.SpecItems, mine.SpecPending);
                SortedSetMerge.PendingNext(asSorted.SpecItems, theirs.SpecPending);
                bool mineEnded = !mine.MoveNext(), theirsEnded = !theirs.MoveNext();
                SpecSetOps.UnionWhole(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                SpecSetOps.UnionSorted(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                while (!mineEnded && !theirsEnded)
                {
#if PAL
                    Pal.Invariant(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                    Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, originalSnapshot.Value));
#endif
                    Pal.Invariant(mine.SpecReady && theirs.SpecReady &&
                                  Pal.Implies(mineEnded, mine.SpecPending.Length == 0) &&
                                  Pal.Implies(theirsEnded, theirs.SpecPending.Length == 0) &&
                                  SortedSetMerge.Suffix(this.SpecItems, mine.SpecPending) && SortedSetMerge.Suffix(asSorted.SpecItems, theirs.SpecPending) &&
                                  Pal.Implies(!mineEnded, mine.SpecCurrentIn && mine.SpecPending.Length < this.SpecItems.Length &&
                                      Pal.Same(SpecSearchTree.RootKey(mine.SpecCurrentTree, this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1]),
                                               this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1])) &&
                                  Pal.Implies(!theirsEnded, theirs.SpecCurrentIn && theirs.SpecPending.Length < asSorted.SpecItems.Length &&
                                      Pal.Same(SpecSearchTree.RootKey(theirs.SpecCurrentTree, asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1]),
                                               asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1])) &&
                                  merged.Length == this.SpecItems.Length + asSorted.SpecItems.Length && 0 <= c &&
                                  c <= this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1) +
                                       asSorted.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1) &&
                                  Pal.Concat(SortedSetMerge.Take(Pal.Contents(merged), c),
                                      SpecSetOps.Union(this.SpecComparer,
                                          SortedSetMerge.Drop(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1)),
                                          SortedSetMerge.Drop(asSorted.SpecItems, asSorted.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1)))) ==
                                  SpecSetOps.Union(this.SpecComparer, this.SpecItems, asSorted.SpecItems));
                    Pal.Decreases(mine.SpecPending.Length + (mineEnded ? 0 : 1) + theirs.SpecPending.Length + (theirsEnded ? 0 : 1));
                    SpecSetOps.UnionStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                        this.SpecItems.Length - mine.SpecPending.Length - 1, asSorted.SpecItems.Length - theirs.SpecPending.Length - 1);
                    int comp = Comparer.Compare(mine.Current, theirs.Current);
                    if (comp < 0)
                    {
                        SpecSetOps.PushPrefix(Pal.Contents(merged), c, this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1],
                            SpecSetOps.Union(this.SpecComparer,
                                SortedSetMerge.Drop(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length),
                                SortedSetMerge.Drop(asSorted.SpecItems, asSorted.SpecItems.Length - theirs.SpecPending.Length - 1)));
                        merged[c++] = mine.Current;
                        SortedSetMerge.PendingNext(this.SpecItems, mine.SpecPending);
                        mineEnded = !mine.MoveNext();
                    }
                    else if (comp == 0)
                    {
                        SpecSetOps.PushPrefix(Pal.Contents(merged), c, asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1],
                            SpecSetOps.Union(this.SpecComparer,
                                SortedSetMerge.Drop(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length),
                                SortedSetMerge.Drop(asSorted.SpecItems, asSorted.SpecItems.Length - theirs.SpecPending.Length)));
                        merged[c++] = theirs.Current;
                        SortedSetMerge.PendingNext(this.SpecItems, mine.SpecPending);
                        mineEnded = !mine.MoveNext();
                        SortedSetMerge.PendingNext(asSorted.SpecItems, theirs.SpecPending);
                        theirsEnded = !theirs.MoveNext();
                    }
                    else
                    {
                        SpecSetOps.PushPrefix(Pal.Contents(merged), c, asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1],
                            SpecSetOps.Union(this.SpecComparer,
                                SortedSetMerge.Drop(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length - 1),
                                SortedSetMerge.Drop(asSorted.SpecItems, asSorted.SpecItems.Length - theirs.SpecPending.Length)));
                        merged[c++] = theirs.Current;
                        SortedSetMerge.PendingNext(asSorted.SpecItems, theirs.SpecPending);
                        theirsEnded = !theirs.MoveNext();
                    }
                }

                SpecSetOps.UnionRest(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                    this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1),
                    asSorted.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1));
                if (!mineEnded || !theirsEnded)
                {
                    Enumerator remaining = (mineEnded ? theirs : mine);
                    do
                    {
#if PAL
                        Pal.Invariant(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                        Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, originalSnapshot.Value));
#endif
                        Pal.Invariant(remaining.SpecReady &&
                                      SortedSetMerge.Suffix(mineEnded ? asSorted.SpecItems : this.SpecItems, remaining.SpecPending) &&
                                      Pal.Implies(!Pal.Broke(), remaining.SpecCurrentIn &&
                                          remaining.SpecPending.Length < (mineEnded ? asSorted.SpecItems.Length : this.SpecItems.Length) &&
                                          (mineEnded
                                              ? Pal.Same(SpecSearchTree.RootKey(remaining.SpecCurrentTree, asSorted.SpecItems[asSorted.SpecItems.Length - remaining.SpecPending.Length - 1]),
                                                         asSorted.SpecItems[asSorted.SpecItems.Length - remaining.SpecPending.Length - 1])
                                              : Pal.Same(SpecSearchTree.RootKey(remaining.SpecCurrentTree, this.SpecItems[this.SpecItems.Length - remaining.SpecPending.Length - 1]),
                                                         this.SpecItems[this.SpecItems.Length - remaining.SpecPending.Length - 1]))) &&
                                      Pal.Implies(Pal.Broke(), remaining.SpecPending.Length == 0) &&
                                      merged.Length == this.SpecItems.Length + asSorted.SpecItems.Length && 0 <= c &&
                                      c + remaining.SpecPending.Length + (Pal.Broke() ? 0 : 1) <= merged.Length &&
                                      Pal.Concat(SortedSetMerge.Take(Pal.Contents(merged), c),
                                          mineEnded
                                              ? SortedSetMerge.Drop(asSorted.SpecItems, asSorted.SpecItems.Length - remaining.SpecPending.Length - (Pal.Broke() ? 0 : 1))
                                              : SortedSetMerge.Drop(this.SpecItems, this.SpecItems.Length - remaining.SpecPending.Length - (Pal.Broke() ? 0 : 1))) ==
                                      SpecSetOps.Union(this.SpecComparer, this.SpecItems, asSorted.SpecItems));
                        Pal.Decreases(remaining.SpecPending.Length);
                        SpecSetOps.PushRest(Pal.Contents(merged), c, mineEnded ? asSorted.SpecItems : this.SpecItems,
                            (mineEnded ? asSorted.SpecItems.Length : this.SpecItems.Length) - remaining.SpecPending.Length - 1);
                        merged[c++] = remaining.Current;
                        SortedSetMerge.PendingNext(mineEnded ? asSorted.SpecItems : this.SpecItems, remaining.SpecPending);
                    }
                    while (remaining.MoveNext());
                }
                SpecSetOps.RestDone(SortedSetMerge.Take(Pal.Contents(merged), c), mineEnded ? asSorted.SpecItems : this.SpecItems);
                Pal.Assert(c <= merged.Length &&
                           SortedSetMerge.Take(Pal.Contents(merged), c) == SpecSetOps.Union(this.SpecComparer, this.SpecItems, asSorted.SpecItems));

                // now merged has all c elements

                // safe to gc the root, we  have all the elements
#if PAL
                Ghost<Node?> previousRoot = root;
                Ghost<Seq<T>> unionItems = SpecSetOps.Union(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                Ghost<SpecTree<(T, bool)>> builtTree = SpecSearchTree.Build(Pal.Contents(merged), 0, c - 1, SpecTree.Leaf<(T, bool)>());
                SortedSetConstructionProof.Empty<T>(null);
#endif
                root = null;

                root = ConstructRootFromSortedArray(merged, 0, c - 1, null);
#if PAL
                Ghost<SortedSetLabels<T>> builtLabels = SortedSetConstructionProof.Label(root, builtTree, Perm.Full);
                Pal.Assert(SpecSearchTree.Keys(SortedSetOwnership.Values(builtLabels.Value)) == unionItems.Value);
                SortedSetConstructionProof.Adopt(previousRoot, root, ownershipState, builtLabels);
                ownershipState = SortedSetConstruction.Adopted(ownershipState, builtLabels);
#endif
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
        [GhostArg("SpecTree<(T, bool)> redTree")]
        [Requires("SortedSetConstruction.Holds(redNode, redTree, Perm.Full)")]
        [Requires("SpecSearchTree.IsRedLeaf(redTree)")]
        [Requires("startIndex <= endIndex || redNode == null")]
        [Ensures("Pal.Contents(arr) == Pal.Old(Pal.Contents(arr))")]
        [Ensures("SortedSetConstruction.Holds(Result, SpecSearchTree.Build(Pal.Contents(arr), startIndex, endIndex, redTree), Perm.Full)")]
        [Ensures("Pal.Implies(redNode == null, SpecSearchTree.IsRedBlack(SpecSearchTree.Build(Pal.Contents(arr), startIndex, endIndex, redTree)) && SpecSearchTree.Keys(SpecSearchTree.Build(Pal.Contents(arr), startIndex, endIndex, redTree)) == Pal.Slice(Pal.Contents(arr), startIndex, endIndex + 1))")]
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

#if PAL
            Ghost<Seq<T>> buildItems = Pal.Contents(arr);
            Ghost<SpecTree<(T, bool)>> red = Pal.Ghost<SpecTree<(T, bool)>>("redTree");
            SortedSetConstructionProof.Cases<T>(redNode, red);
#endif
            int size = endIndex - startIndex + 1;
            Pal.Assert(size == endIndex - startIndex + 1);
#if PAL
            Ghost<SpecTree<(T, bool)>> built = SpecSearchTree.Build(buildItems.Value, startIndex, endIndex, red.Value);
#endif
            Node root;

            switch (size)
            {
                case 0:
#if PAL
                    SortedSetConstructionProof.EmptyBuild<T>(redNode, red, buildItems, (SpecInt)startIndex, (SpecInt)endIndex);
                    SortedSetConstruction.BuildFacts(buildItems.Value, startIndex, endIndex, red.Value);
#endif
                    return null;
                case 1:
                    root = new Node(arr[startIndex], NodeColor.Black);
                    if (redNode != null)
                    {
                        root.Left = redNode;
                    }
#if PAL
                    SortedSetConstructionProof.Empty<T>(null);
                    SortedSetConstructionProof.SealLeftInput<T>(root, redNode, red, SpecTree.Leaf<(T, bool)>(), built);
                    SortedSetConstruction.BuildFacts(buildItems.Value, startIndex, endIndex, red.Value);
                    return root;
#else
                    break;
#endif
                case 2:
                    Pal.Assert(endIndex == startIndex + 1);
                    root = new Node(arr[startIndex], NodeColor.Black);
                    root.Right = new Node(arr[endIndex], NodeColor.Black);
                    root.Right.ColorRed();
#if PAL
                    SortedSetConstructionProof.SealRightLeaf<T>(root, SortedSetConstruction.Leaf(buildItems.Value[endIndex], true));
#endif
                    if (redNode != null)
                    {
                        root.Left = redNode;
                    }
#if PAL
                    SortedSetConstructionProof.SealLeftInput<T>(root, redNode, red,
                        SortedSetConstruction.Leaf(buildItems.Value[endIndex], true), built);
                    SortedSetConstruction.BuildFacts(buildItems.Value, startIndex, endIndex, red.Value);
                    return root;
#else
                    break;
#endif
                case 3:
                    Pal.Assert(endIndex == startIndex + 2);
                    root = new Node(arr[startIndex + 1], NodeColor.Black);
                    root.Left = new Node(arr[startIndex], NodeColor.Black);
                    root.Right = new Node(arr[endIndex], NodeColor.Black);
                    if (redNode != null)
                    {
                        root.Left.Left = redNode;
                    }
#if PAL
                    SortedSetConstructionProof.Empty<T>(null);
                    SortedSetConstructionProof.SealLeftChild<T>(root, redNode, red,
                        SpecTree.Leaf<(T, bool)>(),
                        SpecTree.Branch(red.Value, (buildItems.Value[startIndex], false), SpecTree.Leaf<(T, bool)>()));
                    SortedSetConstructionProof.SealRightLeaf<T>(root, SortedSetConstruction.Leaf(buildItems.Value[endIndex], false));
                    SortedSetConstructionProof.SealAs<T>(root,
                        SpecTree.Branch(red.Value, (buildItems.Value[startIndex], false), SpecTree.Leaf<(T, bool)>()),
                        SortedSetConstruction.Leaf(buildItems.Value[endIndex], false), built);
                    SortedSetConstruction.BuildFacts(buildItems.Value, startIndex, endIndex, red.Value);
                    return root;
#else
                    break;
#endif
                default:
                    int midpt = ((startIndex + endIndex) / 2);
                    Pal.Assert(2 * midpt <= startIndex + endIndex && startIndex + endIndex <= 2 * midpt + 1);
                    Pal.Assert(startIndex + 1 <= midpt && midpt + 1 < endIndex);
                    Pal.Assert(size % 2 != 0 || midpt + 2 <= endIndex);
#if PAL
                    Pal.Assert(size >= 4);
                    SortedSetConstruction.BuildStep(buildItems.Value, startIndex, endIndex, midpt, size % 2 == 0, red.Value);
#endif
                    root = new Node(arr[midpt], NodeColor.Black);
                    root.Left = ConstructRootFromSortedArray(arr, startIndex, midpt - 1, redNode);
#if PAL
                    // root is a local, unchanged by either static recursive call;
                    // evaluating this receiver after the condition has no effects.
                    if (size % 2 == 0)
                    {
                        root.Right = ConstructRootFromSortedArray(arr, midpt + 2, endIndex,
                            SortedSetConstructionProof.PrepareFresh(new Node(arr[midpt + 1], NodeColor.Red)));
                        SortedSetConstructionProof.SealAs<T>(root,
                            SpecSearchTree.Build(buildItems.Value, startIndex, midpt - 1, red.Value),
                            SpecSearchTree.Build(buildItems.Value, midpt + 2, endIndex, SortedSetConstruction.Leaf(buildItems.Value[midpt + 1], true)),
                            built);
                        Pal.Assert(Pal.Contents(arr) == Pal.Old(Pal.Contents(arr)));
                        SortedSetConstruction.BuildFacts(buildItems.Value, startIndex, endIndex, red.Value);
                        return root;
                    }
                    else
                    {
                        SortedSetConstructionProof.Empty<T>(null);
                        root.Right = ConstructRootFromSortedArray(arr, midpt + 1, endIndex, null);
                        SortedSetConstructionProof.SealAs<T>(root,
                            SpecSearchTree.Build(buildItems.Value, startIndex, midpt - 1, red.Value),
                            SpecSearchTree.Build(buildItems.Value, midpt + 1, endIndex, SpecTree.Leaf<(T, bool)>()),
                            built);
                        Pal.Assert(Pal.Contents(arr) == Pal.Old(Pal.Contents(arr)));
                        SortedSetConstruction.BuildFacts(buildItems.Value, startIndex, endIndex, red.Value);
                        return root;
                    }
#else
                    root.Right = size % 2 == 0 ?
                        ConstructRootFromSortedArray(arr, midpt + 2, endIndex, new Node(arr[midpt + 1], NodeColor.Red)) :
                        ConstructRootFromSortedArray(arr, midpt + 1, endIndex, null);
                    Pal.Assert(Pal.Contents(arr) == Pal.Old(Pal.Contents(arr)));
                    break;
#endif

            }

#if !PAL
            return root;
#endif
        }

        // The merge keeps the elements of `other` that compare equal to one of this set's
        // (`SetInter.inter`, taking them in `other`'s order).
        [Requires("@this.SpecComparer == other.SpecComparer")]
        // ConstructRootFromSortedArray's midpoint overflows past 2^30 elements.
        [Requires("@this.SpecItems.Length <= 1073741824")]
        [Ensures("@this.SpecItems == SpecSetInter.Inter(@this.SpecComparer, Pal.Old(@this.SpecItems), Pal.Old(other.SpecItems))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer) && other.SpecItems == Pal.Old(other.SpecItems) && other.SpecComparer == Pal.Old(other.SpecComparer)")]
        [Rlimit(30)]
        [Fuel(0, 0)]
        public virtual void IntersectWith([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);
#if PAL
            Ghost<SortedSetSnapshot<T>> originalSnapshot = SortedSetOwnership.Snapshot(this.SpecSnapshot);
#endif

            SpecSetInter.InterLeftEmpty(this.SpecComparer, this.SpecItems, ((SortedSet<T>)other).SpecItems);
            if (Count == 0)
                return;

            if (other == this)
                return;

            // HashSet<T> optimizations can't be done until equality comparers and comparers are related

            // Technically, this would work as well with an ISorted<T>
            SortedSet<T>? asSorted = other as SortedSet<T>;
            TreeSubSet? treeSubset = this as TreeSubSet;

            if (treeSubset != null)
            {
                // The contract makes `this` a SortedSet<T> itself (R27.1), not a view.
                Pal.Unreachable();
                VersionCheck();
            }

            if (asSorted != null && treeSubset == null && HasEqualComparer(asSorted))
            {
                // First do a merge sort to an array.
                T[] merged = new T[this.Count];
                int c = 0;
                Enumerator mine = this.GetEnumerator();
                Enumerator theirs = asSorted.GetEnumerator();
                SortedSetMerge.Whole(this.SpecItems);
                SortedSetMerge.Whole(asSorted.SpecItems);
                SortedSetMerge.PendingNext(this.SpecItems, mine.SpecPending);
                SortedSetMerge.PendingNext(asSorted.SpecItems, theirs.SpecPending);
                bool mineEnded = !mine.MoveNext(), theirsEnded = !theirs.MoveNext();
                T? max = Max;
                SpecSetInter.InterWhole(this.SpecComparer, this.SpecItems, asSorted.SpecItems);

#if PAL
                while (!mineEnded && !theirsEnded)
#else
                while (!mineEnded && !theirsEnded && Comparer.Compare(theirs.Current, max) <= 0)
#endif
                {
#if PAL
                    Pal.Invariant(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                    Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, originalSnapshot.Value));
#endif
                    Pal.Invariant(mine.SpecReady && theirs.SpecReady &&
                                  Pal.Implies(mineEnded, mine.SpecPending.Length == 0) &&
                                  Pal.Implies(theirsEnded, theirs.SpecPending.Length == 0) &&
                                  SortedSetMerge.Suffix(this.SpecItems, mine.SpecPending) && SortedSetMerge.Suffix(asSorted.SpecItems, theirs.SpecPending) &&
                                  Pal.Implies(!mineEnded, mine.SpecCurrentIn && mine.SpecPending.Length < this.SpecItems.Length &&
                                      Pal.Same(SpecSearchTree.RootKey(mine.SpecCurrentTree, this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1]),
                                               this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1])) &&
                                  Pal.Implies(!theirsEnded, theirs.SpecCurrentIn && theirs.SpecPending.Length < asSorted.SpecItems.Length &&
                                      Pal.Same(SpecSearchTree.RootKey(theirs.SpecCurrentTree, asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1]),
                                               asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1])) &&
                                  this.SpecItems.Length > 0 && Pal.Same(max, this.SpecItems[this.SpecItems.Length - 1]) &&
                                  merged.Length == this.SpecItems.Length && 0 <= c &&
                                  c <= this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1) &&
                                  Pal.Concat(SortedSetMerge.Take(Pal.Contents(merged), c),
                                      SpecSetInter.Inter(this.SpecComparer,
                                          SortedSetMerge.Drop(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1)),
                                          SortedSetMerge.Drop(asSorted.SpecItems, asSorted.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1)))) ==
                                  SpecSetInter.Inter(this.SpecComparer, this.SpecItems, asSorted.SpecItems));
#if PAL
                    Pal.Invariant(Pal.Implies(Pal.Broke(),
                        !mineEnded && !theirsEnded &&
                        Pal.Compare(this.SpecComparer,
                            asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1], max!) > 0));
#endif
                    Pal.Decreases(mine.SpecPending.Length + (mineEnded ? 0 : 1) + theirs.SpecPending.Length + (theirsEnded ? 0 : 1));
#if PAL
                    // The final original guard operand is evaluated exactly once,
                    // before any executable action from the original loop body.
                    if (Comparer.Compare(theirs.Current, max) > 0)
                    {
                        break;
                    }
#endif
                    SpecSetInter.InterStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                        this.SpecItems.Length - mine.SpecPending.Length - 1, asSorted.SpecItems.Length - theirs.SpecPending.Length - 1);
                    int comp = Comparer.Compare(mine.Current, theirs.Current);
                    if (comp < 0)
                    {
                        SortedSetMerge.PendingNext(this.SpecItems, mine.SpecPending);
                        mineEnded = !mine.MoveNext();
                    }
                    else if (comp == 0)
                    {
                        SpecSetInter.PushPrefix(Pal.Contents(merged), c, asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1],
                            SpecSetInter.Inter(this.SpecComparer,
                                SortedSetMerge.Drop(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length),
                                SortedSetMerge.Drop(asSorted.SpecItems, asSorted.SpecItems.Length - theirs.SpecPending.Length)));
                        merged[c++] = theirs.Current;
                        SortedSetMerge.PendingNext(this.SpecItems, mine.SpecPending);
                        mineEnded = !mine.MoveNext();
                        SortedSetMerge.PendingNext(asSorted.SpecItems, theirs.SpecPending);
                        theirsEnded = !theirs.MoveNext();
                    }
                    else
                    {
                        SortedSetMerge.PendingNext(asSorted.SpecItems, theirs.SpecPending);
                        theirsEnded = !theirs.MoveNext();
                    }
                }

                // now merged has all c elements
                SpecSetInter.InterFinish(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                    this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1),
                    asSorted.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1),
                    SortedSetMerge.Take(Pal.Contents(merged), c));
                SpecSetInter.InterSorted(this.SpecComparer, this.SpecItems, asSorted.SpecItems);

                // safe to gc the root, we  have all the elements
#if PAL
                Ghost<Node?> previousRoot = root;
                Ghost<Seq<T>> intersectionItems = SpecSetInter.Inter(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                Ghost<SpecTree<(T, bool)>> builtTree = SpecSearchTree.Build(Pal.Contents(merged), 0, c - 1, SpecTree.Leaf<(T, bool)>());
                SortedSetConstructionProof.Empty<T>(null);
#endif
                root = null;

                root = ConstructRootFromSortedArray(merged, 0, c - 1, null);
#if PAL
                Ghost<SortedSetLabels<T>> builtLabels = SortedSetConstructionProof.Label(root, builtTree, Perm.Full);
                Pal.Assert(SpecSearchTree.Keys(SortedSetOwnership.Values(builtLabels.Value)) == intersectionItems.Value);
                SortedSetConstructionProof.Adopt(previousRoot, root, ownershipState, builtLabels);
                ownershipState = SortedSetConstruction.Adopted(ownershipState, builtLabels);
#endif
                count = c;
                version++;
            }
            else
            {
                // The contract requires `other` to be a SortedSet<T> with this set's comparer,
                // and this set is not a view (R27.1), so the branch above was taken.
                Pal.Unreachable();
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

        // The range test and the early `break` are sound only when `other` is sorted by this
        // set's comparer, so the contract requires the same comparer (doc/translation.md R27.47).
        [Requires("@this.SpecComparer == other.SpecComparer")]
        [Ensures("@this.SpecItems == SpecSetOps.Except(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), Pal.Old(other.SpecItems))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer) && other.SpecItems == Pal.Old(other.SpecItems) && other.SpecComparer == Pal.Old(other.SpecComparer)")]
        [Rlimit(8)]
        public void ExceptWith([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
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
                    Ghost<Seq<T>> s0 = this.SpecItems;
                    SpecSetOps.ExceptWhole(this.SpecComparer, s0.Value, asSorted.SpecItems);
                    foreach (T item in other)
                    {
#if PAL
                        Pal.Invariant(SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                        Pal.Invariant(SortedSetOwnership.Valid(root, ownershipState, comparer, count, version));
#endif
                        Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecReady &&
                                      Pal.Enumerator<Enumerator>(item).SpecPending ==
                                          Pal.Slice(asSorted.SpecItems, asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length, asSorted.SpecItems.Length) &&
                                      s0.Value.Length > 0 && Pal.Same(min, s0.Value[0]) && Pal.Same(max, s0.Value[s0.Value.Length - 1]) &&
                                      this.SpecComparer == Pal.Old(this.SpecComparer) &&
                                      this.SpecItems == SpecSetOps.Except(this.SpecComparer, s0.Value,
                                          Pal.Slice(asSorted.SpecItems, 0, asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length)) &&
                                      Pal.Implies(Pal.Broke(), this.SpecItems == SpecSetOps.Except(this.SpecComparer, s0.Value, asSorted.SpecItems)));
                        Pal.Decreases(Pal.Enumerator<Enumerator>(item).SpecPending.Length);
                        SpecSetOps.ExceptStep(this.SpecComparer, s0.Value, asSorted.SpecItems,
                            asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                        SpecSetOps.ExceptSkip(this.SpecComparer, s0.Value, asSorted.SpecItems,
                            asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                        SpecSetOps.ExceptBreak(this.SpecComparer, s0.Value, asSorted.SpecItems,
                            asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                        if (comparer.Compare(item, min) < 0)
                            continue;
                        if (comparer.Compare(item, max) > 0)
                            break;
                        Remove(item);
                    }
                    SpecSetOps.ExceptWhole(this.SpecComparer, s0.Value, asSorted.SpecItems);
                }
                else
                {
                    SpecSetOps.ExceptDisjoint(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                }
            }
            else
            {
                // The contract requires `other` to be a SortedSet<T> with this set's comparer.
                Pal.Unreachable();
                RemoveAllElements(other);
            }
        }

        // An empty set takes `UnionWith`'s path, which gives the same set (`SymmetricExceptUnionEmpty`);
        // `other` is a different object (R27.50).
        [Requires("@this.SpecComparer == other.SpecComparer")]
        [Requires("@this.SpecItems.Length + other.SpecItems.Length <= 1073741824")]
        [Ensures("@this.SpecItems == SpecSetOps.SymmetricExcept(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), Pal.Old(other.SpecItems))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer) && other.SpecItems == Pal.Old(other.SpecItems) && other.SpecComparer == Pal.Old(other.SpecComparer)")]
        public void SymmetricExceptWith([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (Count == 0)
            {
                SpecSetOps.SymmetricExceptUnionEmpty(this.SpecComparer, this.SpecItems, ((SortedSet<T>)other).SpecItems);
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
                // The contract requires `other` to be a SortedSet<T> with this set's comparer.
                Pal.Unreachable();
                int length;
                T[] elements = EnumerableHelpers.ToArray(other, out length);
                Array.Sort(elements, 0, length, Comparer);
                SymmetricExceptWithSameComparer(elements, length);
            }
        }

        // Each element of `other` is looked up and added under this set's comparer, so the
        // contract requires the same comparer (doc/translation.md R27.47); the counts bound
        // the size the set can reach, so that `Add` cannot overflow `count`.
        [Requires("@this.SpecComparer == other.SpecComparer")]
        [Requires("@this.SpecItems.Length + other.SpecItems.Length <= int.MaxValue")]
        [Ensures("@this.SpecItems == SpecSetOps.SymmetricExcept(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), Pal.Old(other.SpecItems))")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer) && other.SpecItems == Pal.Old(other.SpecItems) && other.SpecComparer == Pal.Old(other.SpecComparer)")]
        [Rlimit(8)]
        private void SymmetricExceptWithSameComparer(SortedSet<T> other)
        {
            Debug.Assert(other != null);
            Debug.Assert(HasEqualComparer(other));

            foreach (T item in other)
            {
                Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecReady &&
                              Pal.Enumerator<Enumerator>(item).SpecPending ==
                                  Pal.Slice(other.SpecItems, other.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length, other.SpecItems.Length) &&
                              this.SpecComparer == Pal.Old(this.SpecComparer) &&
                              this.SpecItems == SpecSetOps.SymmetricExcept(Pal.Old(this.SpecComparer), Pal.Old(this.SpecItems),
                                  Pal.Slice(other.SpecItems, 0, other.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length)));
                Pal.Decreases(Pal.Enumerator<Enumerator>(item).SpecPending.Length);
                SpecSetOps.SymmetricExceptStep(Pal.Old(this.SpecComparer), Pal.Old(this.SpecItems), other.SpecItems,
                    other.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                SpecSetOps.SymmetricExceptLength(Pal.Old(this.SpecComparer), Pal.Old(this.SpecItems), other.SpecItems,
                    other.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                bool result = Contains(item) ? Remove(item) : Add(item);
                Debug.Assert(result);
            }
            SpecSetOps.SymmetricExceptWhole(Pal.Old(this.SpecComparer), Pal.Old(this.SpecItems), other.SpecItems);
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

        // R37.10. `other` is a SortedSet<T> (R27.46) under any comparer that `Equals` does not
        // confuse with this set's (R27.47). With the same comparer the fast path decides; with
        // another, the counts do.
        [Requires("Pal.Implies(SpecSortDedupe.ComparerEquals(@this.SpecComparer, other.SpecComparer), @this.SpecComparer == other.SpecComparer)")]
        [Ensures("Result == SortedSetCount.AllHit(@this.SpecComparer, other.SpecItems, @this.SpecItems)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        public bool IsSubsetOf([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (Count == 0)
            {
                return true;
            }

            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                SortedSetCount.SortedHits(this.SpecComparer, asSorted.SpecItems, this.SpecItems);
                if (Count > asSorted.Count)
                    return false;
                return IsSubsetOfSortedSetWithSameComparer(asSorted);
            }
            else
            {
                // Worst case: I mark every element in my set and see if I've counted all of them. O(M log N).
                ElementCount result = CheckUniqueAndUnfoundElements(other, false);
                SortedSetCount.CountsDecide(this.SpecComparer, this.SpecItems, asSorted!.SpecItems);
                return result.UniqueCount == Count && result.UnfoundCount >= 0;
            }
        }

        // R32.14. The view `prunedOther` borrows `asSorted`: `Contains` on it is membership
        // in `asSorted` within this set's range, which holds every element of this set.
        [Requires("@this.SpecComparer == asSorted.SpecComparer")]
        [Ensures("Result == SpecSetOps.AllIn(asSorted.SpecComparer, asSorted.SpecItems, @this.SpecItems)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes) && asSorted.SpecNodes == Pal.Old(asSorted.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer) && asSorted.SpecComparer == Pal.Old(asSorted.SpecComparer)")]
        [Rlimit(8)]
        private bool IsSubsetOfSortedSetWithSameComparer(SortedSet<T> asSorted)
        {
            SpecSetOps.SortedBounds(asSorted.SpecComparer, this.SpecItems, 0);
            SortedSet<T> prunedOther = asSorted.GetViewBetween(Min, Max);
            SpecSetOps.AllInWhole(asSorted.SpecComparer, asSorted.SpecItems, this.SpecItems);
            foreach (T item in this)
            {
                Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecReady &&
                              Pal.Enumerator<Enumerator>(item).SpecPending ==
                                  Pal.Slice(this.SpecItems, this.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length, this.SpecItems.Length) &&
                              ((TreeSubSet)prunedOther).SpecCoherent && ((TreeSubSet)prunedOther).SpecLowerActive && ((TreeSubSet)prunedOther).SpecUpperActive &&
                              Pal.Same(((TreeSubSet)prunedOther).SpecMin, this.SpecItems.Length > 0 ? this.SpecItems[0] : default(T)) &&
                              Pal.Same(((TreeSubSet)prunedOther).SpecMax, this.SpecItems.Length > 0 ? this.SpecItems[this.SpecItems.Length - 1] : default(T)) &&
                              (Pal.Returned()
                                  ? !Pal.ReturnValue<bool>() && !SpecSetOps.AllIn(asSorted.SpecComparer, asSorted.SpecItems, this.SpecItems)
                                  : SpecSetOps.AllIn(asSorted.SpecComparer, asSorted.SpecItems, this.SpecItems) ==
                                    SpecSetOps.AllIn(asSorted.SpecComparer, asSorted.SpecItems, Pal.Enumerator<Enumerator>(item).SpecPending)));
                Pal.Decreases(Pal.Enumerator<Enumerator>(item).SpecPending.Length);
                SpecSetOps.AllInStep(asSorted.SpecComparer, asSorted.SpecItems, this.SpecItems,
                    this.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                SpecSetOps.SortedBounds(asSorted.SpecComparer, this.SpecItems,
                    this.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                if (!prunedOther.Contains(item))
                    return false;
            }
            SpecSetOps.AllInStep(asSorted.SpecComparer, asSorted.SpecItems, this.SpecItems, this.SpecItems.Length);
            return true;
        }

        // R37.10. As `IsSubsetOf`; and some item of `other` is not in this set.
        [Requires("Pal.Implies(SpecSortDedupe.ComparerEquals(@this.SpecComparer, other.SpecComparer), @this.SpecComparer == other.SpecComparer)")]
        [Ensures("Result == (SortedSetCount.AllHit(@this.SpecComparer, other.SpecItems, @this.SpecItems) && !SortedSetCount.AllHit(@this.SpecComparer, @this.SpecItems, other.SpecItems))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        public bool IsProperSubsetOf([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
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
                SortedSetCount.SortedHits(this.SpecComparer, asSorted.SpecItems, this.SpecItems);
                if (Count >= asSorted.Count)
                    return false;
                return IsSubsetOfSortedSetWithSameComparer(asSorted);
            }

            // Worst case: I mark every element in my set and see if I've counted all of them. O(M log N).
            ElementCount result = CheckUniqueAndUnfoundElements(other, false);
            SortedSetCount.CountsDecide(this.SpecComparer, this.SpecItems, asSorted!.SpecItems);
            return result.UniqueCount == Count && result.UnfoundCount > 0;
        }

        // R32.14. The view `pruned` borrows this set: `Contains` on it is membership in this
        // set within `asSorted`'s range, which holds every element of `asSorted`.
        [Requires("@this.SpecComparer == other.SpecComparer")]
        [Ensures("Result == SpecSetOps.AllIn(@this.SpecComparer, @this.SpecItems, other.SpecItems)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Rlimit(8)]
        public bool IsSupersetOf([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            if (other is ICollection c && c.Count == 0)
                return true;

            // do it one way for HashSets
            // another for sorted sets with the same comparer
            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                SpecSetOps.AllInLength(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                if (Count < asSorted.Count)
                    return false;
                SpecSetOps.SortedBounds(this.SpecComparer, asSorted.SpecItems, 0);
                SortedSet<T> pruned = GetViewBetween(asSorted.Min, asSorted.Max);
                SpecSetOps.AllInWhole(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                foreach (T item in asSorted)
                {
                    Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecReady &&
                                  Pal.Enumerator<Enumerator>(item).SpecPending ==
                                      Pal.Slice(asSorted.SpecItems, asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length, asSorted.SpecItems.Length) &&
                                  ((TreeSubSet)pruned).SpecCoherent && ((TreeSubSet)pruned).SpecLowerActive && ((TreeSubSet)pruned).SpecUpperActive &&
                                  Pal.Same(((TreeSubSet)pruned).SpecMin, asSorted.SpecItems.Length > 0 ? asSorted.SpecItems[0] : default(T)) &&
                                  Pal.Same(((TreeSubSet)pruned).SpecMax, asSorted.SpecItems.Length > 0 ? asSorted.SpecItems[asSorted.SpecItems.Length - 1] : default(T)) &&
                                  (Pal.Returned()
                                      ? !Pal.ReturnValue<bool>() && !SpecSetOps.AllIn(this.SpecComparer, this.SpecItems, asSorted.SpecItems)
                                      : SpecSetOps.AllIn(this.SpecComparer, this.SpecItems, asSorted.SpecItems) ==
                                        SpecSetOps.AllIn(this.SpecComparer, this.SpecItems, Pal.Enumerator<Enumerator>(item).SpecPending)));
                    Pal.Decreases(Pal.Enumerator<Enumerator>(item).SpecPending.Length);
                    SpecSetOps.AllInStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                        asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                    SpecSetOps.SortedBounds(this.SpecComparer, asSorted.SpecItems,
                        asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                    if (!pruned.Contains(item))
                        return false;
                }
                SpecSetOps.AllInStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems, asSorted.SpecItems.Length);
                return true;
            }

            // The contract requires `other` to be a SortedSet<T> with this set's comparer,
            // so the branch above was taken (doc/translation.md R27.46-R27.49).
            Pal.Unreachable();

            // and a third for everything else
            return ContainsAllElements(other);
        }

        // R32.14. As `IsSupersetOf`, with the counts compared first.
        // R37.10. Every item of `other` is in this set, and some item of this set is not in
        // `other`; `other` as in `IsSubsetOf`.
        [Requires("Pal.Implies(SpecSortDedupe.ComparerEquals(@this.SpecComparer, other.SpecComparer), @this.SpecComparer == other.SpecComparer)")]
        [Ensures("Result == (SortedSetCount.AllHit(@this.SpecComparer, @this.SpecItems, other.SpecItems) && !SortedSetCount.AllHit(@this.SpecComparer, other.SpecItems, @this.SpecItems))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Rlimit(8)]
        public bool IsProperSupersetOf([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
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
                SortedSetCount.SortedHits(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                if (asSorted.Count >= Count)
                    return false;
                SpecSetOps.SortedBounds(this.SpecComparer, asSorted.SpecItems, 0);
                SortedSet<T> pruned = GetViewBetween(asSorted.Min, asSorted.Max);
                SpecSetOps.AllInWhole(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                foreach (T item in asSorted)
                {
                    Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecReady &&
                                  Pal.Enumerator<Enumerator>(item).SpecPending ==
                                      Pal.Slice(asSorted.SpecItems, asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length, asSorted.SpecItems.Length) &&
                                  ((TreeSubSet)pruned).SpecCoherent && ((TreeSubSet)pruned).SpecLowerActive && ((TreeSubSet)pruned).SpecUpperActive &&
                                  Pal.Same(((TreeSubSet)pruned).SpecMin, asSorted.SpecItems.Length > 0 ? asSorted.SpecItems[0] : default(T)) &&
                                  Pal.Same(((TreeSubSet)pruned).SpecMax, asSorted.SpecItems.Length > 0 ? asSorted.SpecItems[asSorted.SpecItems.Length - 1] : default(T)) &&
                                  (Pal.Returned()
                                      ? !Pal.ReturnValue<bool>() && !SpecSetOps.AllIn(this.SpecComparer, this.SpecItems, asSorted.SpecItems)
                                      : SpecSetOps.AllIn(this.SpecComparer, this.SpecItems, asSorted.SpecItems) ==
                                        SpecSetOps.AllIn(this.SpecComparer, this.SpecItems, Pal.Enumerator<Enumerator>(item).SpecPending)));
                    Pal.Decreases(Pal.Enumerator<Enumerator>(item).SpecPending.Length);
                    SpecSetOps.AllInStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                        asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                    SpecSetOps.SortedBounds(this.SpecComparer, asSorted.SpecItems,
                        asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                    if (!pruned.Contains(item))
                        return false;
                }
                SpecSetOps.AllInStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems, asSorted.SpecItems.Length);
                return true;
            }

            // Worst case: I mark every element in my set and see if I've counted all of them. O(M log N).
            // slight optimization, put it into a HashSet and then check can do it in O(N+M)
            // but slower in better cases + wastes space
            ElementCount result = CheckUniqueAndUnfoundElements(other, true);
            SortedSetCount.CountsDecide(this.SpecComparer, this.SpecItems, asSorted!.SpecItems);
            return result.UniqueCount < Count && result.UnfoundCount == 0;
        }

        // R37.10. Each set holds every item of the other under this set's comparer; `other` as
        // in `IsSubsetOf`. With the same comparer, two strictly sorted sequences are position by
        // position equal exactly when they hold the same set (`SortedSetCount.sorted_hits`).
        [Requires("Pal.Implies(SpecSortDedupe.ComparerEquals(@this.SpecComparer, other.SpecComparer), @this.SpecComparer == other.SpecComparer)")]
        [Ensures("Result == (SortedSetCount.AllHit(@this.SpecComparer, other.SpecItems, @this.SpecItems) && SortedSetCount.AllHit(@this.SpecComparer, @this.SpecItems, other.SpecItems))")]
        [Rlimit(8)]
        public bool SetEquals([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);

            SortedSet<T>? asSorted = other as SortedSet<T>;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                Enumerator mine = GetEnumerator();
                Enumerator theirs = asSorted.GetEnumerator();
                bool mineEnded = !mine.MoveNext();
                bool theirsEnded = !theirs.MoveNext();
                SortedSetCount.SortedHits(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                SpecSetCompare.SameKeysWhole(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                while (!mineEnded && !theirsEnded)
                {
                    Pal.Invariant(mine.SpecReady && theirs.SpecReady &&
                                  (Pal.Returned()
                                      ? !Pal.ReturnValue<bool>() && !SpecSetCompare.SameKeys(this.SpecComparer, this.SpecItems, asSorted.SpecItems)
                                      : Pal.Implies(mineEnded, mine.SpecPending.Length == 0) &&
                                        Pal.Implies(theirsEnded, theirs.SpecPending.Length == 0) &&
                                        mine.SpecPending == Pal.Slice(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length, this.SpecItems.Length) &&
                                        theirs.SpecPending == Pal.Slice(asSorted.SpecItems, asSorted.SpecItems.Length - theirs.SpecPending.Length, asSorted.SpecItems.Length) &&
                                        Pal.Implies(!mineEnded, mine.SpecCurrentIn && mine.SpecPending.Length < this.SpecItems.Length &&
                                            Pal.Same(SpecSearchTree.RootKey(mine.SpecCurrentTree, this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1]),
                                                     this.SpecItems[this.SpecItems.Length - mine.SpecPending.Length - 1])) &&
                                        Pal.Implies(!theirsEnded, theirs.SpecCurrentIn && theirs.SpecPending.Length < asSorted.SpecItems.Length &&
                                            Pal.Same(SpecSearchTree.RootKey(theirs.SpecCurrentTree, asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1]),
                                                     asSorted.SpecItems[asSorted.SpecItems.Length - theirs.SpecPending.Length - 1])) &&
                                        SpecSetCompare.SameKeys(this.SpecComparer, this.SpecItems, asSorted.SpecItems) ==
                                        SpecSetCompare.SameKeys(this.SpecComparer,
                                            Pal.Slice(this.SpecItems, this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1), this.SpecItems.Length),
                                            Pal.Slice(asSorted.SpecItems, asSorted.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1), asSorted.SpecItems.Length))));
                    Pal.Decreases(mine.SpecPending.Length + (mineEnded ? 0 : 1));
                    SpecSetCompare.SameKeysStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                        this.SpecItems.Length - mine.SpecPending.Length - 1, asSorted.SpecItems.Length - theirs.SpecPending.Length - 1);
                    if (Comparer.Compare(mine.Current, theirs.Current) != 0)
                    {
                        return false;
                    }
                    mineEnded = !mine.MoveNext();
                    theirsEnded = !theirs.MoveNext();
                }
                SpecSetCompare.SameKeysStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                    this.SpecItems.Length - mine.SpecPending.Length - (mineEnded ? 0 : 1),
                    asSorted.SpecItems.Length - theirs.SpecPending.Length - (theirsEnded ? 0 : 1));
                return mineEnded && theirsEnded;
            }

            // Worst case: I mark every element in my set and see if I've counted all of them. O(size of the other collection).
            ElementCount result = CheckUniqueAndUnfoundElements(other, true);
            SortedSetCount.CountsDecide(this.SpecComparer, this.SpecItems, asSorted!.SpecItems);
            return result.UniqueCount == Count && result.UnfoundCount == 0;
        }

        // The range test is sound only when `other` is sorted by this set's comparer: with a
        // comparer whose `Equals` says two different orders are equal, `Overlaps` may answer
        // `false` for sets that share an element (doc/translation.md R27.47).
        [Requires("@this.SpecComparer == other.SpecComparer")]
        [Ensures("Result == SpecSetOps.Overlaps(@this.SpecComparer, @this.SpecItems, other.SpecItems)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Rlimit(8)]
        [Frac("p")]
        public bool Overlaps([Exactly(typeof(SortedSet<>))] IEnumerable<T> other)
        {
            ArgumentNullException.ThrowIfNull(other);
#if PAL
            Ghost<SortedSetSnapshot<T>> originalSnapshot = SortedSetOwnership.Snapshot(this.SpecSnapshot);
#endif

            if (Count == 0)
                return false;

            if (other is ICollection<T> c && c.Count == 0)
                return false;

            SortedSet<T>? asSorted = other as SortedSet<T>;
#if PAL
            Ghost<SortedSetSnapshot<T>> originalOtherSnapshot = SortedSetOwnership.Snapshot(asSorted!.SpecSnapshot);
            bool rangesDisjoint = false;
            if (asSorted != null && HasEqualComparer(asSorted))
            {
                if (comparer.Compare(Min, asSorted.Max) > 0)
                {
                    rangesDisjoint = true;
                }
                else
                {
                    rangesDisjoint = comparer.Compare(Max, asSorted.Min) < 0;
                }
                Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Pal.Permission()));
                Pal.Join(SortedSetState.Matches(root, ownershipState, comparer, count, version, originalSnapshot.Value));
                Pal.Join(Pal.Same(originalOtherSnapshot.Value, SortedSetOwnership.Snapshot(asSorted.SpecSnapshot)));
                Pal.Join(Pal.Implies(rangesDisjoint,
                    Pal.Compare(this.SpecComparer, this.SpecItems[0], asSorted.SpecItems[asSorted.SpecItems.Length - 1]) > 0 ||
                    Pal.Compare(this.SpecComparer, this.SpecItems[this.SpecItems.Length - 1], asSorted.SpecItems[0]) < 0));
            }
            Pal.Join(SortedSetOwnership.Owner(root, ownershipState, Pal.Permission()));
            Pal.Join(SortedSetState.Matches(root, ownershipState, comparer, count, version, originalSnapshot.Value));
            Pal.Join(Pal.Same(originalOtherSnapshot.Value, SortedSetOwnership.Snapshot(asSorted!.SpecSnapshot)));
            Pal.Join(Pal.Implies(rangesDisjoint,
                Pal.Compare(this.SpecComparer, this.SpecItems[0], asSorted!.SpecItems[asSorted.SpecItems.Length - 1]) > 0 ||
                Pal.Compare(this.SpecComparer, this.SpecItems[this.SpecItems.Length - 1], asSorted.SpecItems[0]) < 0));
            if (rangesDisjoint)
#else
            if (asSorted != null && HasEqualComparer(asSorted) && (comparer.Compare(Min, asSorted.Max) > 0 || comparer.Compare(Max, asSorted.Min) < 0))
#endif
            {
                SpecSetOps.OverlapsDisjoint(this.SpecComparer, this.SpecItems, asSorted.SpecItems);
                return false;
            }

            SpecSetOps.OverlapsWhole(this.SpecComparer, this.SpecItems, asSorted!.SpecItems);
            foreach (T item in other)
            {
#if PAL
                Pal.Invariant(SortedSetOwnership.Owner(root, ownershipState, Pal.Permission()));
                Pal.Invariant(SortedSetState.Matches(root, ownershipState, comparer, count, version, originalSnapshot.Value));
#endif
                Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecReady &&
                              Pal.Enumerator<Enumerator>(item).SpecPending ==
                                  Pal.Slice(asSorted.SpecItems, asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length, asSorted.SpecItems.Length) &&
                              (Pal.Returned()
                                  ? Pal.ReturnValue<bool>() && SpecSetOps.Overlaps(this.SpecComparer, this.SpecItems, asSorted.SpecItems)
                                  : SpecSetOps.Overlaps(this.SpecComparer, this.SpecItems, asSorted.SpecItems) ==
                                    SpecSetOps.Overlaps(this.SpecComparer, this.SpecItems, Pal.Enumerator<Enumerator>(item).SpecPending)));
                Pal.Decreases(Pal.Enumerator<Enumerator>(item).SpecPending.Length);
                SpecSetOps.OverlapsStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems,
                    asSorted.SpecItems.Length - Pal.Enumerator<Enumerator>(item).SpecPending.Length - 1);
                if (Contains(item))
                {
                    return true;
                }
            }

            SpecSetOps.OverlapsStep(this.SpecComparer, this.SpecItems, asSorted.SpecItems, asSorted.SpecItems.Length);
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
        // pal: §37. As dotnet/runtime#133116 rewrites it, `BitHelper` over `stackalloc`ed or
        // allocated ints included (R37.2). At a view the method's body is checked again
        // (R32.13): the range is the view's, and the tree its range root.
        [Requires("Pal.Contents(other).Length <= int.MaxValue")]
        [Ensures("Result.UnfoundCount >= 0 && (Result.UnfoundCount > 0) == (SortedSetCount.UnfoundAll(@this.SpecComparer, @this.SpecItems, Pal.Contents(other)) > 0)")]
        [Ensures("Pal.Implies(!returnIfUnfound || Result.UnfoundCount == 0, Result.UniqueCount == SortedSetCount.FoundAll(@this.SpecComparer, @this.SpecItems, Pal.Contents(other)))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Requires("@this.SpecCoherent && @this.SpecCountOk && Pal.Contents(other).Length <= int.MaxValue", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Result.UnfoundCount >= 0 && (Result.UnfoundCount > 0) == (SortedSetCount.UnfoundRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems, Pal.Contents(other)) > 0)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Implies(!returnIfUnfound || Result.UnfoundCount == 0, Result.UniqueCount == SortedSetCount.FoundRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems, Pal.Contents(other)))", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
        [Rlimit(20)]
        private unsafe ElementCount CheckUniqueAndUnfoundElements(IEnumerable<T> other, bool returnIfUnfound)
        {
            ElementCount result;

            // need special case in case this has no elements.
            if (Count == 0)
            {
                int numElementsInOther = 0;
                foreach (T item in other)
                {
                    Pal.Invariant(Pal.Implies(!Pal.Broke(), numElementsInOther == 0 && Pal.Index(item) == 0) &&
                                  Pal.Implies(Pal.Broke(), numElementsInOther == 1 && Pal.Contents(other).Length > 0));
                    numElementsInOther++;
                    // break right away, all we want to know is whether other has 0 or 1 elements
                    break;
                }
                SortedSetCount.EmptyCounts(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, SpecSearchTree.Keys(this.SpecRangeTree), Pal.Contents(other));
                SortedSetCount.Counts(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, SpecSearchTree.Keys(this.SpecRangeTree), Pal.Contents(other));
                result.UniqueCount = 0;
                result.UnfoundCount = numElementsInOther;
                return result;
            }

            int maxHeight = GetApproximateMaxHeight();
#if PAL
            Ghost<SortedSetLabels<T>> labels = this is TreeSubSet view ? view.ReadLabels : this.SpecLabels;
            SortedSetOwnershipProof.RootFacts(labels);
            Ghost<SpecTree<(T, bool)>> indexTree = SortedSetOwnership.Lookup(labels.Value, root);
            Ghost<SortedSetSnapshot<T>> snapshot = this is TreeSubSet subset
                ? subset.ReadSnapshot
                : SortedSetOwnership.Snapshot(this.SpecSnapshot);
            Ghost<SortedSetRetainedPayload<T>> preservedViewState = SortedSetRetainedHolder.Payload(ownershipState);
#endif

            // maxHeight = 12 needs 8kb for bitHelper, use fallback with HashSet if maxHeight > 12 to mitigate
            // this by limiting memory complexity to O(n).
            if (maxHeight > 12)
            {
                return CheckUniqueAndUnfoundElementsFallback(other, returnIfUnfound);
            }

            // A perfect tree of height H has H^2 - 1 nodes; (round up to H^2).
            SortedSetCount.ShiftOne(maxHeight); // pal: 1 << maxHeight == 2^maxHeight, no overflow
            int indexLimit = (1 << maxHeight);
            int intArrayLength = BitHelper.ToIntArrayLength(indexLimit);
            BitHelperBits.WordsCover(indexLimit);

            Span<int> span = stackalloc int[StackAllocThreshold];
            BitHelper bitHelper = (uint)intArrayLength <= StackAllocThreshold ?
                new BitHelper(span.Slice(0, intArrayLength), clear: true) :
                new BitHelper(new int[intArrayLength], clear: false);

            // count of items in other not found in this
            int unfoundCount = 0;
            // count of unique items in other found in this
            int uniqueFoundCount = 0;

            SortedSetCount.LookupIntro(comparer, this.SpecRangeTree, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa);
#if PAL
            SortedSetCount.FitsPow2(comparer, indexTree.Value, maxHeight);
            BitHelperBits.ZeroBits(Pal.Contents(bitHelper.Span));
            SortedSetCount.LoopStart(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, indexTree.Value, SpecSearchTree.Keys(this.SpecRangeTree), BitHelperBits.Bits(Pal.Contents(bitHelper.Span)), Pal.Contents(other));
            if (this is TreeSubSet)
                SortedSetOwnershipProof.Empty<T>();
#endif
            foreach (T item in other)
            {
#if PAL
                Pal.Invariant(this is TreeSubSet
                    ? SortedSetOwnership.Owner(null, SortedSetOwnership.Empty<T>(), Perm.Full)
                    : SortedSetOwnership.Owner(root, ownershipState, Perm.Full));
                Pal.Invariant(this is TreeSubSet || SortedSetState.Matches(root, ownershipState, comparer, count, version, snapshot.Value));
                Pal.Invariant(this.SpecRangeReady);
                Pal.Invariant(!(this is TreeSubSet) ||
                    Pal.Same(ownershipState, SortedSetRetainedHolder.State(preservedViewState.Value)));
                Pal.Invariant(root == null || SortedSetOwnership.Member(labels.Value, root));
                Pal.Invariant(SortedSetCount.Lookup(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, indexTree.Value, SpecSearchTree.Keys(this.SpecRangeTree)) &&
                              SortedSetCount.Fits(comparer, indexTree.Value, indexLimit) &&
                              this.SpecRangeComparer == Pal.Old(this.SpecRangeComparer) && this.SpecRangeLo == Pal.Old(this.SpecRangeLo) && this.SpecRangeHi == Pal.Old(this.SpecRangeHi) &&
                              indexTree.Value == SortedSetOwnership.Lookup(labels.Value, root) && indexTree.Value.Height <= 12 && Pal.Contents(bitHelper.Span).Length == intArrayLength && indexLimit <= 32 * intArrayLength &&
                              0 <= uniqueFoundCount && 0 <= unfoundCount && uniqueFoundCount + unfoundCount <= Pal.Index(item) &&
                              Pal.Implies(!Pal.Broke(),
                                  Pal.Implies(returnIfUnfound, unfoundCount == 0) &&
                                  SortedSetCount.LoopInv(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, indexTree.Value, SpecSearchTree.Keys(this.SpecRangeTree),
                                                         BitHelperBits.Bits(Pal.Contents(bitHelper.Span)), Pal.Contents(other), Pal.Index(item), uniqueFoundCount, unfoundCount)) &&
                              Pal.Implies(Pal.Broke(), returnIfUnfound && unfoundCount > 0 &&
                                  SortedSetCount.UnfoundS(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, SpecSearchTree.Keys(this.SpecRangeTree), Pal.Contents(other)) > 0));
#endif
                // pal: FIX for #133116. `InternalIndexOf` searches the view's range-root subtree, which may hold
                // out-of-range nodes; without the range check, an out-of-range item counts as found.
                int index = IsWithinRange(item) ? InternalIndexOf(item) : -1;
#if PAL
                SortedSetCount.LoopStep(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, indexTree.Value, SpecSearchTree.Keys(this.SpecRangeTree),
                                        BitHelperBits.Bits(Pal.Contents(bitHelper.Span)), Pal.Contents(other), Pal.Index(item) - 1, uniqueFoundCount, unfoundCount);
#endif
                if ((uint)index < (uint)indexLimit) // Equivalent of "index >= 0 && index < indexLimit"
                {
                    BitHelperBits.MarkedBits(Pal.Contents(bitHelper.Span), index);
                    BitHelperBits.SetBits(Pal.Contents(bitHelper.Span), index);
                    if (!bitHelper.IsMarked(index))
                    {
                        // item hasn't been seen yet
                        bitHelper.MarkBit(index);
                        uniqueFoundCount++;
                    }
                }
                else if (index < 0)
                {
                    unfoundCount++;
                    if (returnIfUnfound)
                    {
#if PAL
                        SortedSetCount.LoopDone(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, indexTree.Value, SpecSearchTree.Keys(this.SpecRangeTree),
                                                BitHelperBits.Bits(Pal.Contents(bitHelper.Span)), Pal.Contents(other), Pal.Index(item), uniqueFoundCount, unfoundCount);
#endif
                        break;
                    }
                }
                else
                {
                    // pal: R37.4. Dead: every position is below `indexLimit` (`Fits`).
                    Pal.Unreachable();
                    // Safe guard: since maxHeight isn't guaranteed, we might need to grow the bitHelper.
                    indexLimit = (int)BitOperations.RoundUpToPowerOf2((uint)index);
                    intArrayLength = BitHelper.ToIntArrayLength(indexLimit);
                    Span<int> newSpan = new int[intArrayLength];
                    bitHelper.Span.CopyTo(newSpan);
                    bitHelper = new BitHelper(newSpan, clear: false);
                }
            }

#if PAL
            if (this is TreeSubSet)
                SortedSetOwnershipProof.ConsumeEmpty<T>();
            SortedSetCount.LoopEnd(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, indexTree.Value, SpecSearchTree.Keys(this.SpecRangeTree),
                                   BitHelperBits.Bits(Pal.Contents(bitHelper.Span)), Pal.Contents(other), uniqueFoundCount, unfoundCount, returnIfUnfound && unfoundCount > 0);
#endif
            SortedSetCount.Counts(comparer, this.SpecRangeLo, this.SpecRangeHi, this.SpecRangeLa, this.SpecRangeUa, SpecSearchTree.Keys(this.SpecRangeTree), Pal.Contents(other));
            result.UniqueCount = uniqueFoundCount;
            result.UnfoundCount = unfoundCount;
            return result;
        }

        // pal: R37.3. Trusted: `HashSet<Node>` (reference equality on nodes) is not modelled.
        // Its contract is the bitmap version's.
        [Admit]
        [Requires("Pal.Contents(other).Length <= int.MaxValue")]
        [Ensures("Result.UnfoundCount >= 0 && (Result.UnfoundCount > 0) == (SortedSetCount.UnfoundAll(@this.SpecComparer, @this.SpecItems, Pal.Contents(other)) > 0)")]
        [Ensures("Pal.Implies(!returnIfUnfound || Result.UnfoundCount == 0, Result.UniqueCount == SortedSetCount.FoundAll(@this.SpecComparer, @this.SpecItems, Pal.Contents(other)))")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Requires("@this.SpecCoherent && @this.SpecRootOk && @this.version == @this._underlying.SpecVersion && Pal.Contents(other).Length <= int.MaxValue", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Result.UnfoundCount >= 0 && (Result.UnfoundCount > 0) == (SortedSetCount.UnfoundRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems, Pal.Contents(other)) > 0)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Implies(!returnIfUnfound || Result.UnfoundCount == 0, Result.UniqueCount == SortedSetCount.FoundRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems, Pal.Contents(other)))", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
        private ElementCount CheckUniqueAndUnfoundElementsFallback(IEnumerable<T> other, bool returnIfUnfound)
        {
            ElementCount result;
            HashSet<Node>? seenNodes = null;
            // count of items in other not found in this
            int unfoundCount = 0;
            // count of unique items in other found in this
            int uniqueFoundCount = 0;

            foreach (T item in other)
            {
                Node? node = FindNode(item);
                if (node != null)
                {
                    seenNodes ??= new HashSet<Node>();
                    if (seenNodes.Add(node))
                    {
                        uniqueFoundCount++;
                    }
                }
                else
                {
                    unfoundCount++;
                    if (returnIfUnfound)
                    {
                        break;
                    }
                }
            }

            result.UniqueCount = uniqueFoundCount;
            result.UnfoundCount = unfoundCount;
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
#if PAL
                Ghost<SortedSetLabels<T>> labels = SortedSetOwnership.Active(ownershipState);
                SortedSetOwnershipProof.RootFacts(labels);
#endif
                if (root == null)
                {
                    return default;
                }

                Node current = root;
#if PAL
                SortedSetOwnershipProof.OpenNode(root, ownershipState, current, Pal.Permission());
#endif
                while (current.Left != null)
                {
#if PAL
                    Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                    Pal.Invariant(SortedSetOwnership.Window(root, ownershipState, current, Pal.Permission())!);
                    Pal.Invariant(current != null && SortedSetOwnership.Member(labels.Value, current));
                    Pal.Invariant(Pal.Forall((T d) => Pal.Same(SpecSearchTree.Leftmost(SortedSetOwnership.Lookup(labels.Value, current), d),
                                                               SpecSearchTree.Leftmost(SortedSetOwnership.Values(labels.Value), d))));
#endif
                    current = current.Left;
#if PAL
                    SortedSetOwnershipProof.CloseNode(root, ownershipState, Pal.Permission());
                    SortedSetOwnershipProof.OpenNode(root, ownershipState, current, Pal.Permission());
#endif
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
#if PAL
                Ghost<SortedSetLabels<T>> labels = SortedSetOwnership.Active(ownershipState);
                SortedSetOwnershipProof.RootFacts(labels);
#endif
                if (root == null)
                {
                    return default;
                }

                Node current = root;
#if PAL
                SortedSetOwnershipProof.OpenNode(root, ownershipState, current, Pal.Permission());
#endif
                while (current.Right != null)
                {
#if PAL
                    Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                    Pal.Invariant(SortedSetOwnership.Window(root, ownershipState, current, Pal.Permission())!);
                    Pal.Invariant(current != null && SortedSetOwnership.Member(labels.Value, current));
                    Pal.Invariant(Pal.Forall((T d) => Pal.Same(SpecSearchTree.Rightmost(SortedSetOwnership.Lookup(labels.Value, current), d),
                                                               SpecSearchTree.Rightmost(SortedSetOwnership.Values(labels.Value), d))));
#endif
                    current = current.Right;
#if PAL
                    SortedSetOwnershipProof.CloseNode(root, ownershipState, Pal.Permission());
                    SortedSetOwnershipProof.OpenNode(root, ownershipState, current, Pal.Permission());
#endif
                }

                return current.Item;
            }
        }

        [Ensures("Pal.Yielded<T>() == Pal.Reverse(@this.SpecItems)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Rlimit(4)]
        public IEnumerable<T> Reverse()
        {
            Enumerator e = new Enumerator(this, reverse: true);
            while (e.MoveNext())
            {
                Pal.Invariant(e.SpecReady && Pal.Concat(Pal.Yielded<T>(), e.SpecPending) == Pal.Reverse(this.SpecItems));
                Pal.Decreases(this.SpecItems.Length - Pal.Yielded<T>().Length);
                yield return e.Current;
            }
        }

        [Throws(typeof(ArgumentException), "Pal.Compare(@this.SpecComparer, lowerValue, upperValue) > 0")]
        [Ensures("Pal.Same(Result.SpecMin, lowerValue) && Pal.Same(Result.SpecMax, upperValue) && Result.SpecLowerActive && Result.SpecUpperActive")]
        [Ensures("Result.SpecRootOk && Result.SpecCoherent")]
        [Ensures("Pal.Implies(@this.SpecVersion != -1, Result.SpecCountOk)")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes) && @this.SpecComparer == Pal.Old(@this.SpecComparer) && @this.SpecVersion == Pal.Old(@this.SpecVersion)")]
        [return: Exactly(typeof(SortedSet<>.TreeSubSet))]
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

        [Plain]
        internal sealed class Node
        {
            [Ensures("SortedSetOwnership.Fresh(Result, item, color)")]
            public Node(T item, NodeColor color)
            {
                Item = item;
                Color = color;
            }

            [GhostArg("SortedSetNullableSnapshot<T> snapshot"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.NullableRaw(node, snapshot, permission)")]
            [Ensures("Result == (node != null && !SortedSetOwnership.NullableRed(snapshot))")]
            public static bool IsNonNullBlack(Node? node)
            {
                if (node != null)
                {
#if PAL
                    SortedSetOwnershipProof.OpenNullable(node, Pal.Ghost<SortedSetNullableSnapshot<T>>("snapshot"), Pal.Ghost<Perm>("permission"));
#endif
                    bool result = node.IsBlack;
#if PAL
                    SortedSetOwnershipProof.CloseNullable(node, Pal.Ghost<SortedSetNullableSnapshot<T>>("snapshot"), Pal.Ghost<Perm>("permission"));
#endif
                    return result;
                }
                return false;
            }

            [GhostArg("SortedSetNullableSnapshot<T> snapshot"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.NullableRaw(node, snapshot, permission)")]
            [Ensures("Result == SortedSetOwnership.NullableRed(snapshot)")]
            public static bool IsNonNullRed(Node? node)
            {
                if (node != null)
                {
#if PAL
                    SortedSetOwnershipProof.OpenNullable(node, Pal.Ghost<SortedSetNullableSnapshot<T>>("snapshot"), Pal.Ghost<Perm>("permission"));
#endif
                    bool result = node.IsRed;
#if PAL
                    SortedSetOwnershipProof.CloseNullable(node, Pal.Ghost<SortedSetNullableSnapshot<T>>("snapshot"), Pal.Ghost<Perm>("permission"));
#endif
                    return result;
                }
#if PAL
                SortedSetOwnershipProof.NullCase(node, Pal.Ghost<SortedSetNullableSnapshot<T>>("snapshot"), Pal.Ghost<Perm>("permission"));
#endif
                return false;
            }

            [GhostArg("SortedSetNullableSnapshot<T> snapshot"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.NullableRaw(node, snapshot, permission)")]
            [Ensures("Result == !SortedSetOwnership.NullableRed(snapshot)")]
            public static bool IsNullOrBlack(Node? node)
            {
                if (node == null)
                {
#if PAL
                    SortedSetOwnershipProof.NullCase(node, Pal.Ghost<SortedSetNullableSnapshot<T>>("snapshot"), Pal.Ghost<Perm>("permission"));
#endif
                    return true;
                }
#if PAL
                SortedSetOwnershipProof.OpenNullable(node, Pal.Ghost<SortedSetNullableSnapshot<T>>("snapshot"), Pal.Ghost<Perm>("permission"));
#endif
                bool result = node.IsBlack;
#if PAL
                SortedSetOwnershipProof.CloseNullable(node, Pal.Ghost<SortedSetNullableSnapshot<T>>("snapshot"), Pal.Ghost<Perm>("permission"));
#endif
                return result;
            }

            public T Item { get; set; }

            public Node? Left { get; set; }

            public Node? Right { get; set; }

            public NodeColor Color { get; set; }

            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.Raw(@this, snapshot, permission)")]
            [Ensures("Result == !SortedSetOwnership.Red(snapshot)")]
            public bool IsBlack => Color == NodeColor.Black;

            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.Raw(@this, snapshot, permission)")]
            [Ensures("Result == SortedSetOwnership.Red(snapshot)")]
            public bool IsRed => Color == NodeColor.Red;

            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNullableSnapshot<T> left"), GhostArg("SortedSetNullableSnapshot<T> right"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.Raw(@this, snapshot, permission)")]
            [Preserves("SortedSetOwnership.NullableRaw(SortedSetOwnership.Left(snapshot), left, permission)")]
            [Preserves("SortedSetOwnership.NullableRaw(SortedSetOwnership.Right(snapshot), right, permission)")]
            [Ensures("Result == (!SortedSetOwnership.Red(snapshot) && !SortedSetOwnership.NullableRed(left) && !SortedSetOwnership.NullableRed(right))")]
            public bool Is2Node => IsBlack && IsNullOrBlack(Left) && IsNullOrBlack(Right);

            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNullableSnapshot<T> left"), GhostArg("SortedSetNullableSnapshot<T> right"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.Raw(@this, snapshot, permission)")]
            [Preserves("SortedSetOwnership.NullableRaw(SortedSetOwnership.Left(snapshot), left, permission)")]
            [Preserves("SortedSetOwnership.NullableRaw(SortedSetOwnership.Right(snapshot), right, permission)")]
            [Ensures("Result == (SortedSetOwnership.NullableRed(left) && SortedSetOwnership.NullableRed(right))")]
            public bool Is4Node => IsNonNullRed(Left) && IsNonNullRed(Right);

            [GhostArg("SortedSetNodeSnapshot<T> snapshot")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(@this, SortedSetOwnership.Recolor(snapshot, false), Perm.Full)")]
            public void ColorBlack() => Color = NodeColor.Black;

            [GhostArg("SortedSetNodeSnapshot<T> snapshot")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(@this, SortedSetOwnership.Recolor(snapshot, true), Perm.Full)")]
            public void ColorRed() => Color = NodeColor.Red;

            [Rlimit(10), GhostArg("SortedSetLabels<T> labels")]
            [Preserves("SortedSetOwnership.Owns(labels, Perm.Full)")]
            [Requires("SortedSetOwnership.Top(labels) == @this")]
            [Requires("SortedSetClone.Size(labels) <= count")]
            [Ensures("SortedSetConstruction.Holds(Result, SortedSetOwnership.Values(labels), Perm.Full)")]
            public Node DeepClone(int count)
            {
#if DEBUG
                Debug.Assert(count == GetCount());
#endif
#if PAL
                Ghost<SortedSetLabels<T>> source = Pal.Ghost<SortedSetLabels<T>>("labels");
                SortedSetCloneProof.OpenSource(source, this);
#endif
                Node newRoot = ShallowClone();
#if PAL
                SortedSetCloneProof.Seed(source, this, newRoot);
                SortedSetCloneBudget remaining = SortedSetClone.Initial(source);
#endif

                var pendingNodes = new Stack<(Node source, Node target)>(2 * Log2(count) + 2);
                pendingNodes.Push((this, newRoot));
#if PAL
                SortedSetCloneProof.Start(source, this, newRoot, pendingNodes.Items, remaining);
                SortedSetCloneProof.Facts(source, newRoot, pendingNodes.Items, remaining);
#endif

                while (pendingNodes.TryPop(out var next))
                {
#if PAL
                    Pal.Decreases(SortedSetClone.Value(remaining));
                    Pal.Invariant(SortedSetClone.Cloning(source.Value, newRoot, pendingNodes.Items, SortedSetClone.Value(remaining), Perm.Full));
                    Pal.Invariant(SortedSetClone.Size(source.Value) <= count);
                    Pal.Invariant(pendingNodes.Items.Length <= SortedSetClone.Value(remaining) && SortedSetClone.Value(remaining) <= SortedSetClone.Size(source.Value));
                    Ghost<Seq<(Node, Node)>> prefix = pendingNodes.Items;
                    Ghost<SortedSetCloneWitness<T>> job = SortedSetCloneProof.Pop(source, newRoot, prefix, next, remaining);
                    SortedSetCloneProof.OpenJob(SortedSetClone.Focus(job.Value), next.source, next.target);
#endif
                    Node clonedNode;

                    if (next.source.Left is Node left)
                    {
#if PAL
                        SortedSetCloneProof.OpenSource(SortedSetClone.LeftTree(SortedSetClone.Focus(job.Value)), left);
#endif
                        clonedNode = left.ShallowClone();
                        next.target.Left = clonedNode;
#if PAL
                        SortedSetCloneProof.Seed(SortedSetClone.LeftTree(SortedSetClone.Focus(job.Value)), left, clonedNode);
#endif
                        pendingNodes.Push((left, clonedNode));
#if PAL
                        SortedSetCloneProof.CloseLeft(SortedSetClone.Focus(job.Value), next.source, next.target, prefix, pendingNodes.Items);
#endif
                    }
#if PAL
                    else
                    {
                        SortedSetCloneProof.EmptySource<T>(SortedSetClone.LeftTree(SortedSetClone.Focus(job.Value)));
                        SortedSetCloneProof.CloseLeft(SortedSetClone.Focus(job.Value), next.source, next.target, prefix, pendingNodes.Items);
                    }
                    Pal.Join(SortedSetClone.LeftStage(SortedSetClone.Focus(job.Value), next.target, prefix.Value, pendingNodes.Items, Perm.Full));
                    Pal.Join(SortedSetClone.Restore(source.Value, newRoot, prefix.Value, SortedSetClone.Offset(job.Value), SortedSetClone.Focus(job.Value), next.target, Perm.Full));
                    SortedSetCloneProof.OpenLeft(SortedSetClone.Focus(job.Value), next.source, next.target, prefix, pendingNodes.Items);
#endif

                    if (next.source.Right is Node right)
                    {
#if PAL
                        SortedSetCloneProof.OpenSource(SortedSetClone.RightTree(SortedSetClone.Focus(job.Value)), right);
#endif
                        clonedNode = right.ShallowClone();
                        next.target.Right = clonedNode;
#if PAL
                        SortedSetCloneProof.Seed(SortedSetClone.RightTree(SortedSetClone.Focus(job.Value)), right, clonedNode);
#endif
                        pendingNodes.Push((right, clonedNode));
#if PAL
                        SortedSetCloneProof.CloseComplete(SortedSetClone.Focus(job.Value), next.source, next.target, prefix, pendingNodes.Items);
#endif
                    }
#if PAL
                    else
                    {
                        SortedSetCloneProof.EmptySource<T>(SortedSetClone.RightTree(SortedSetClone.Focus(job.Value)));
                        SortedSetCloneProof.CloseComplete(SortedSetClone.Focus(job.Value), next.source, next.target, prefix, pendingNodes.Items);
                    }
                    Pal.Join(SortedSetClone.Complete(SortedSetClone.Focus(job.Value), next.target, prefix.Value, pendingNodes.Items, Perm.Full));
                    Pal.Join(SortedSetClone.Restore(source.Value, newRoot, prefix.Value, SortedSetClone.Offset(job.Value), SortedSetClone.Focus(job.Value), next.target, Perm.Full));

                    SortedSetCloneProof.FinishTask(source, newRoot, job, next.target, prefix, pendingNodes.Items, remaining);
                    remaining = SortedSetClone.Previous(remaining);
                    SortedSetCloneProof.Facts(source, newRoot, pendingNodes.Items, remaining);
#endif
                }

#if PAL
                SortedSetCloneProof.Finish(source, newRoot, pendingNodes.Items, remaining);
#endif
                return newRoot;
            }

            /// <summary>
            /// Gets the rotation this node should undergo during a removal.
            /// </summary>
            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNodeSnapshot<T> siblingSnapshot"), GhostArg("SortedSetNullableSnapshot<T> siblingLeft"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.Raw(@this, snapshot, permission)")]
            [Preserves("SortedSetOwnership.Raw(sibling, siblingSnapshot, permission)")]
            [Preserves("SortedSetOwnership.NullableRaw(SortedSetOwnership.Left(siblingSnapshot), siblingLeft, permission)")]
            [Ensures("Result == (SortedSetOwnership.NullableRed(siblingLeft) ? (current == SortedSetOwnership.Left(snapshot) ? TreeRotation.RightLeft : TreeRotation.Right) : (current == SortedSetOwnership.Left(snapshot) ? TreeRotation.Left : TreeRotation.LeftRight))")]
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
            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.Raw(@this, snapshot, permission)")]
            [Requires("node == SortedSetOwnership.Left(snapshot) && SortedSetOwnership.Right(snapshot) != null || node == SortedSetOwnership.Right(snapshot) && SortedSetOwnership.Left(snapshot) != null")]
            [Requires("SortedSetOwnership.Left(snapshot) != SortedSetOwnership.Right(snapshot)")]
            [Ensures("Result == (node == SortedSetOwnership.Left(snapshot) ? SortedSetOwnership.Right(snapshot) : SortedSetOwnership.Left(snapshot))")]
            public Node GetSibling(Node node)
            {
                Debug.Assert(node != null);
                Debug.Assert(node == Left ^ node == Right);

                return node == Left ? Right! : Left!;
            }

            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("Perm permission")]
            [Preserves("SortedSetOwnership.Raw(@this, snapshot, permission)")]
            [Ensures("SortedSetOwnership.Fresh(Result, SortedSetOwnership.Item(snapshot), SortedSetOwnership.Color(snapshot))")]
            public Node ShallowClone() => new Node(Item, Color);

            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNodeSnapshot<T> left"), GhostArg("SortedSetNodeSnapshot<T> right")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Left(snapshot), left, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Right(snapshot), right, Perm.Full)")]
            [Requires("SortedSetOwnership.Left(snapshot) != null && SortedSetOwnership.Right(snapshot) != null")]
            [Ensures("SortedSetOwnership.Raw(@this, SortedSetOwnership.Recolor(snapshot, true), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(SortedSetOwnership.Left(snapshot), SortedSetOwnership.Recolor(left, false), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(SortedSetOwnership.Right(snapshot), SortedSetOwnership.Recolor(right, false), Perm.Full)")]
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
            [GhostArg("SortedSetLabels<T> labels"), GhostArg("bool direction"), GhostArg("SortedSet<T>.Node? sibling")]
            [Requires("SortedSetDispatch.Selector(@this, sibling, labels, direction)")]
            [Requires("SortedSetDispatch.CanRotate(rotation, labels)")]
            [Ensures("SortedSetDispatch.After(@this, Result, labels, rotation)")]
            [Ensures("Result != null")]
            public Node? Rotate(TreeRotation rotation)
            {
#if PAL
                SortedSetDispatchProof.CloseSelector(this, Pal.Ghost<Node?>("sibling"), Pal.Ghost<SortedSetLabels<T>>("labels"), Pal.Ghost<bool>("direction"));
                SortedSetDispatchProof.Open(this, Pal.Ghost<SortedSetLabels<T>>("labels"), rotation);
#endif
                Node removeRed;
                switch (rotation)
                {
                    case TreeRotation.Right:
#if PAL
                        SortedSetDispatchProof.Specialize(this, Pal.Ghost<SortedSetLabels<T>>("labels"), rotation, TreeRotation.Right);
#endif
                        removeRed = Left!.Left!;
                        Debug.Assert(removeRed.IsRed);
                        removeRed.ColorBlack();
                        return RotateRight();
                    case TreeRotation.Left:
#if PAL
                        SortedSetDispatchProof.Specialize(this, Pal.Ghost<SortedSetLabels<T>>("labels"), rotation, TreeRotation.Left);
#endif
                        removeRed = Right!.Right!;
                        Debug.Assert(removeRed.IsRed);
                        removeRed.ColorBlack();
                        return RotateLeft();
                    case TreeRotation.RightLeft:
#if PAL
                        SortedSetDispatchProof.Specialize(this, Pal.Ghost<SortedSetLabels<T>>("labels"), rotation, TreeRotation.RightLeft);
#endif
                        Debug.Assert(Right!.Left!.IsRed);
                        return RotateRightLeft();
                    case TreeRotation.LeftRight:
#if PAL
                        SortedSetDispatchProof.Specialize(this, Pal.Ghost<SortedSetLabels<T>>("labels"), rotation, TreeRotation.LeftRight);
#endif
                        Debug.Assert(Left!.Right!.IsRed);
                        return RotateLeftRight();
                    default:
                        Debug.Fail($"{nameof(rotation)}: {rotation} is not a defined {nameof(TreeRotation)} value.");
#if PAL
                        SortedSetDispatchProof.Impossible(this, Pal.Ghost<SortedSetLabels<T>>("labels"), rotation);
#endif
                        return null;
                }
            }

            /// <summary>
            /// Does a left rotation on this tree, making this node the new left child of the current right child.
            /// </summary>
            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNodeSnapshot<T> child")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Right(snapshot), child, Perm.Full)")]
            [Requires("SortedSetOwnership.Right(snapshot) != null")]
            [Ensures("Result == SortedSetOwnership.Right(snapshot)")]
            [Ensures("SortedSetOwnership.Raw(@this, SortedSetOwnership.WithRight(snapshot, SortedSetOwnership.Left(child)), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(Result, SortedSetOwnership.WithLeft(child, @this), Perm.Full)")]
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
            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNodeSnapshot<T> childSnapshot"), GhostArg("SortedSetNodeSnapshot<T> grandSnapshot")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Left(snapshot), childSnapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Right(childSnapshot), grandSnapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Left(snapshot) != null && SortedSetOwnership.Right(childSnapshot) != null")]
            [Ensures("Result == SortedSetOwnership.Right(childSnapshot)")]
            [Ensures("SortedSetOwnership.Raw(@this, SortedSetOwnership.WithLeft(snapshot, SortedSetOwnership.Right(grandSnapshot)), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(SortedSetOwnership.Left(snapshot), SortedSetOwnership.WithRight(childSnapshot, SortedSetOwnership.Left(grandSnapshot)), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(Result, SortedSetOwnership.WithChildren(grandSnapshot, SortedSetOwnership.Left(snapshot), @this), Perm.Full)")]
            [Rlimit(10)]
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
            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNodeSnapshot<T> child")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Left(snapshot), child, Perm.Full)")]
            [Requires("SortedSetOwnership.Left(snapshot) != null")]
            [Ensures("Result == SortedSetOwnership.Left(snapshot)")]
            [Ensures("SortedSetOwnership.Raw(@this, SortedSetOwnership.WithLeft(snapshot, SortedSetOwnership.Right(child)), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(Result, SortedSetOwnership.WithRight(child, @this), Perm.Full)")]
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
            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNodeSnapshot<T> childSnapshot"), GhostArg("SortedSetNodeSnapshot<T> grandSnapshot")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Right(snapshot), childSnapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Left(childSnapshot), grandSnapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Right(snapshot) != null && SortedSetOwnership.Left(childSnapshot) != null")]
            [Ensures("Result == SortedSetOwnership.Left(childSnapshot)")]
            [Ensures("SortedSetOwnership.Raw(@this, SortedSetOwnership.WithRight(snapshot, SortedSetOwnership.Left(grandSnapshot)), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(SortedSetOwnership.Right(snapshot), SortedSetOwnership.WithLeft(childSnapshot, SortedSetOwnership.Right(grandSnapshot)), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(Result, SortedSetOwnership.WithChildren(grandSnapshot, @this, SortedSetOwnership.Right(snapshot)), Perm.Full)")]
            [Rlimit(10)]
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
            [GhostArg("SortedSetNodeSnapshot<T> snapshot"), GhostArg("SortedSetNodeSnapshot<T> left"), GhostArg("SortedSetNodeSnapshot<T> right")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Left(snapshot), left, Perm.Full)")]
            [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Right(snapshot), right, Perm.Full)")]
            [Requires("SortedSetOwnership.Left(snapshot) != null && SortedSetOwnership.Right(snapshot) != null")]
            [Ensures("SortedSetOwnership.Raw(@this, SortedSetOwnership.Recolor(snapshot, false), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(SortedSetOwnership.Left(snapshot), SortedSetOwnership.Recolor(left, true), Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(SortedSetOwnership.Right(snapshot), SortedSetOwnership.Recolor(right, true), Perm.Full)")]
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
            [GhostArg("SortedSetNodeSnapshot<T> snapshot")]
            [Requires("SortedSetOwnership.Raw(@this, snapshot, Perm.Full)")]
            [Ensures("SortedSetOwnership.Raw(@this, child == SortedSetOwnership.Left(snapshot) ? SortedSetOwnership.WithLeft(snapshot, newChild) : SortedSetOwnership.WithRight(snapshot, newChild), Perm.Full)")]
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

            private readonly Stack<Node?> _stack;
            private Node? _current;

            private readonly bool _reverse;

#if PAL
            [Spec] internal Seq<T> SpecPending => SortedSetState.Pending(_reverse, _tree.SpecObservation, _stack.Items);
            [Spec] internal SpecTree<(T, bool)> SpecCurrentTree => SortedSetState.Tree(_tree.SpecObservation, _current);
            [Spec] internal bool SpecCurrentIn => _current != null && SortedSetState.Member(_tree.SpecObservation, _current);
            [Spec] internal bool SpecReady =>
                SortedSetState.Walkable(_tree.SpecObservation, _stack.Items) &&
                SpecPending.Length <= _tree.SpecCount && _version == _tree.SpecVersion;
            // R32.12. What a wrapping struct (SortedDictionary's enumerators) states of this one.
            [Spec] internal bool SpecWalking =>
                SortedSetState.Walkable(_tree.SpecObservation, _stack.Items) && SpecPending.Length <= _tree.SpecCount;
            [Spec] internal bool SpecWalkable => SortedSetState.Walkable(_tree.SpecObservation, _stack.Items);
            [Spec] internal bool SpecFresh => _version == _tree.SpecVersion;
            [Spec] internal bool SpecCurrentOk => _current == null || SortedSetState.Member(_tree.SpecObservation, _current);
            [Spec] internal bool SpecEnded => _current == null;
            [Spec] internal bool SpecCurrentWf => _current != null && SortedSetState.WellFormed(_tree.SpecObservation, _current);
            [Spec] internal Seq<T> SpecInitial => SpecWalk.Keys(_reverse, _tree.SpecNodes);
#else
            [Spec] internal Seq<T> SpecPending => throw new InvalidOperationException("Specification only");
            [Spec] internal SpecTree<(T, bool)> SpecCurrentTree => throw new InvalidOperationException("Specification only");
            [Spec] internal bool SpecCurrentIn => throw new InvalidOperationException("Specification only");
            [Spec] internal bool SpecReady => throw new InvalidOperationException("Specification only");
            [Spec] internal bool SpecWalking => throw new InvalidOperationException("Specification only");
            [Spec] internal bool SpecWalkable => throw new InvalidOperationException("Specification only");
            [Spec] internal bool SpecFresh => throw new InvalidOperationException("Specification only");
            [Spec] internal bool SpecCurrentOk => throw new InvalidOperationException("Specification only");
            [Spec] internal bool SpecEnded => throw new InvalidOperationException("Specification only");
            [Spec] internal bool SpecCurrentWf => throw new InvalidOperationException("Specification only");
            [Spec] internal Seq<T> SpecInitial => throw new InvalidOperationException("Specification only");
#endif

            [Ensures("ReferenceEquals(@this._tree, set) && @this._version == set.SpecVersion && !@this._reverse")]
            [Ensures("@this.SpecWalkable")]
            [Ensures("@this.SpecPending == set.SpecItems")]
            internal Enumerator(SortedSet<T> set)
                : this(set, reverse: false)
            {
            }

            [Ensures("ReferenceEquals(@this._tree, set) && @this._version == set.SpecVersion && @this._reverse == reverse")]
            [Ensures("@this.SpecWalkable")]
            [Ensures("@this.SpecPending == (reverse ? Pal.Reverse(set.SpecItems) : set.SpecItems)")]
            [Wrapping]
            internal Enumerator(SortedSet<T> set, bool reverse)
            {
                _tree = set;
                set.VersionCheck();
                _version = set.version;

                // 2 log(n + 1) is the maximum height.
                _stack = new Stack<Node?>(2 * (int)Log2(set.TotalCount() + 1));
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

            [Rlimit(4)]
            [Fuel(1, 0)]
            [Requires("@this._stack.SpecCount == 0")]
            [Ensures("@this.SpecWalkable")]
            [Ensures("@this.SpecPending == @this.SpecInitial")]
            private void Initialize()
            {
#if PAL
                Ghost<SortedSetObservation<T>> state = _tree.SpecObservation;
                Ghost<SortedSetSnapshot<T>> snapshot = SortedSetOwnership.Snapshot(_tree.SpecSnapshot);
                SortedSetStateProof.Active(_tree.ownershipState);
#endif
                _current = null;
                Node? node = _tree.root;
                Node? next, other;
#if PAL
                SortedSetStateProof.Empty<T>(_reverse, state, _stack.Items);
#endif
                while (node != null)
                {
#if PAL
                    Pal.Decreases(SortedSetState.Tree(state.Value, node).Size);
                    Pal.Invariant(SortedSetOwnership.Owner(_tree.root, _tree.ownershipState, Pal.Permission()));
                    Pal.Invariant(SortedSetState.Matches(_tree.root, _tree.ownershipState,
                        _tree.comparer, _tree.count, _tree.version, snapshot.Value));
                    Pal.Invariant(SortedSetState.WellFormed(state.Value, node) && SortedSetState.Walkable(state.Value, _stack.Items) &&
                                  SpecSearchTree.Keys(SortedSetState.Tree(state.Value, _tree.root)).Length == _tree.count &&
                                  Pal.Concat(SpecWalk.Keys(_reverse, SortedSetState.Tree(state.Value, node)),
                                             SortedSetState.Pending(_reverse, state.Value, _stack.Items)) ==
                                  SpecWalk.Keys(_reverse, SortedSetState.Tree(state.Value, _tree.root)));
                    SortedSetStateProof.Length<T>(_reverse, state, _stack.Items);
                    SortedSetStateProof.Descend<T>(_reverse, state, _stack.Items, node);
                    Pal.Assert(SortedSetState.Tree(state.Value, _tree.root).Size == _tree.count);
                    Pal.Assert(_stack.Items.Length < _tree.count);
                    SortedSetStateProof.OpenOwner(_tree.root, _tree.ownershipState, node, Pal.Permission());
#endif
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
#if PAL
                SortedSetStateProof.Null<T>(state, node);
                Pal.Assert(Pal.Concat(SpecWalk.Keys(_reverse, SortedSetState.Tree(state.Value, node)),
                                      SortedSetState.Pending(_reverse, state.Value, _stack.Items)) ==
                           SortedSetState.Pending(_reverse, state.Value, _stack.Items));
#endif
            }

            [Requires("@this.SpecWalking")]
            [Rlimit(4)]
            [Fuel(1, 0)]
            [Throws(typeof(InvalidOperationException), "@this._version != @this._tree.SpecVersion")]
            [Ensures("@this.SpecWalkable")]
            [Ensures("Result == (Pal.Old(@this.SpecPending).Length > 0)")]
            [Ensures("Pal.Implies(!Result, @this._current == null)")]
            [Ensures("Pal.Implies(Result, @this.SpecCurrentWf && Pal.Same(SpecSearchTree.RootKey(@this.SpecCurrentTree, Pal.Old(@this.SpecPending)[0]), Pal.Old(@this.SpecPending)[0]))")]
            [Ensures("@this.SpecPending == Pal.Slice(Pal.Old(@this.SpecPending), Result ? 1 : 0, Pal.Old(@this.SpecPending).Length)")]
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

#if PAL
                Ghost<SortedSetObservation<T>> state = _tree.SpecObservation;
                Ghost<SortedSetSnapshot<T>> snapshot = SortedSetOwnership.Snapshot(_tree.SpecSnapshot);
                Ghost<Seq<T>> p0 = SortedSetState.Pending(_reverse, state.Value, _stack.Items);
                Pal.Assert(SortedSetState.Pending(_reverse, state.Value, _stack.Items) == Pal.Slice(p0.Value, 0, p0.Value.Length));
                SortedSetStateProof.PopAt<T>(_reverse, state, _stack.Items, p0, 0);
#endif
                _current = _stack.Pop();
#if PAL
                SortedSetStateProof.OpenOwner(_tree.root, _tree.ownershipState, _current, Pal.Permission());
#endif
                Node? node = (_reverse ? _current!.Left : _current!.Right);
#if PAL
                SortedSetStateProof.CloseOwner(_tree.root, _tree.ownershipState, _current, Pal.Permission());
#endif
                Node? next, other;
                while (node != null)
                {
#if PAL
                    Pal.Decreases(SortedSetState.Tree(state.Value, node).Size);
                    Pal.Invariant(SortedSetOwnership.Owner(_tree.root, _tree.ownershipState, Pal.Permission()));
                    Pal.Invariant(SortedSetState.Matches(_tree.root, _tree.ownershipState,
                        _tree.comparer, _tree.count, _tree.version, snapshot.Value));
                    Pal.Invariant(SortedSetState.WellFormed(state.Value, node) && SortedSetState.Walkable(state.Value, _stack.Items) &&
                                  p0.Value.Length <= _tree.count &&
                                  Pal.Concat(SpecWalk.Keys(_reverse, SortedSetState.Tree(state.Value, node)),
                                             SortedSetState.Pending(_reverse, state.Value, _stack.Items)) ==
                                  Pal.Slice(p0.Value, 1, p0.Value.Length));
                    SortedSetStateProof.Length<T>(_reverse, state, _stack.Items);
                    SortedSetStateProof.Descend<T>(_reverse, state, _stack.Items, node);
                    Pal.Assert(Pal.Concat(SpecWalk.Keys(_reverse, SortedSetState.Tree(state.Value, node)),
                        SortedSetState.Pending(_reverse, state.Value, _stack.Items)).Length == p0.Value.Length - 1);
                    Pal.Assert(_stack.Items.Length < p0.Value.Length);
                    SortedSetStateProof.OpenOwner(_tree.root, _tree.ownershipState, node, Pal.Permission());
#endif
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
#if PAL
                SortedSetStateProof.Null<T>(state, node);
                Pal.Assert(Pal.Concat(SpecWalk.Keys(_reverse, SortedSetState.Tree(state.Value, node)),
                                      SortedSetState.Pending(_reverse, state.Value, _stack.Items)) ==
                           SortedSetState.Pending(_reverse, state.Value, _stack.Items));
#endif
                return true;
            }

            [Ensures("true")]
            public void Dispose() { }

            [Requires("@this.SpecCurrentOk")]
            [Ensures("Pal.Implies(!@this.SpecEnded, Pal.Same(Result, SpecSearchTree.RootKey(@this.SpecCurrentTree, Result)))")]
            public T Current
            {
                get
                {
                    if (_current != null)
                    {
#if PAL
                        Ghost<SortedSetObservation<T>> state = _tree.SpecObservation;
                        SortedSetStateProof.Open<T>(state, _current, Pal.Permission());
#endif
                        return _current.Item;
                    }
                    return default(T)!; // Should only happen when accessing Current is undefined behavior
                }
            }

            [Requires("@this.SpecCurrentOk")]
            [Throws(typeof(InvalidOperationException), "@this._current == null")]
            [Ensures("!@this.SpecEnded && Pal.Exists((T v) => Pal.Boxes(Result, v) && Pal.Same(v, SpecSearchTree.RootKey(@this.SpecCurrentTree, v)))")]
            object? IEnumerator.Current
            {
                get
                {
                    if (_current == null)
                    {
                        throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                    }

#if PAL
                    Ghost<SortedSetObservation<T>> state = _tree.SpecObservation;
                    SortedSetStateProof.Open<T>(state, _current, Pal.Permission());
#endif
                    return _current.Item;
                }
            }

            [Ensures("Result == (@this._current == null)")]
            internal bool NotStartedOrEnded => _current == null;

            [Throws(typeof(InvalidOperationException), "@this._version != @this._tree.SpecVersion")]
            [Ensures("@this.SpecWalkable")]
            [Ensures("@this.SpecPending == @this.SpecInitial")]
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
            [Ensures("@this.SpecWalkable")]
            [Ensures("@this.SpecPending == @this.SpecInitial")]
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
#if PAL
                SortedSetOwnershipProof.OpenNode(root, ownershipState, node, Pal.Permission());
#endif
                actualValue = node.Item;
#if PAL
                SortedSetOwnershipProof.CloseNode(root, ownershipState, Pal.Permission());
#endif
                return true;
            }
            actualValue = default;
            return false;
        }

        // Used for set checking operations (using enumerables) that rely on counting
        [Wrapping]
        [Ensures("0 <= Result && Result <= 31")]
        private static int Log2(int value) => BitOperations.Log2((uint)value);

        // The max height is approximate for two reasons:
        // - SortedSet: the limit is based on "Introduction to algorithms" by Thomas H. Cormen,
        //   but this implementation deviates slightly from the one in the book;
        //   it does not immediately do the foxups after Adds/Removes elements, but it is lazily done
        //   on subsequent Adds/Removes. Further proof is needed to guarantee the max height.
        // - TreeSubSet: it is based on _rootLevel which can be out-of-date
        //   (and _underlying.GetApproximateMaxHeight which is approximate).
        // pal: §37. Not approximate: the set's tree is red-black (its `[Refine]`), so its height
        // is at most `2 * floor(log2(n + 1))` (`SortedSetCount.red_black_height`). At a view
        // whose root is current, the view's root is `_rootLevel` below the set's.
        [Ensures("0 <= Result && @this.SpecNodes.Height <= Result")]
        [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Requires("@this.SpecRootOk", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("0 <= Result && SortedSetOwnership.Lookup(@this._underlying.SpecLabels, @this.root).Height <= Result", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("@this.root == Pal.Old(@this.root) && @this.comparer == Pal.Old(@this.comparer)", At = typeof(SortedSet<>.TreeSubSet))]
        [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))", At = typeof(SortedSet<>.TreeSubSet))]
        internal virtual int GetApproximateMaxHeight()
        {
            SortedSetCount.RedBlackHeight(this.SpecNodes);
            // The maximum height of a red-black tree is 2 * log2(n+1).
            // See page 264 of "Introduction to algorithms" by Thomas H. Cormen
            return 2 * BitOperations.Log2((uint)count + 1);
        }

        #endregion
    }
}
