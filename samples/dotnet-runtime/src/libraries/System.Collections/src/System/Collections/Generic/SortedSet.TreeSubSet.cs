// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Diagnostics;
using System.Runtime.Serialization;
using PalLang;

namespace System.Collections.Generic
{
    public partial class SortedSet<T>
    {
        /// <summary>
        /// This class represents a subset view into the tree. Any changes to this view
        /// are reflected in the actual tree. It uses the comparer of the underlying tree.
        /// </summary>
        internal sealed class TreeSubSet : SortedSet<T>, ISerializable, IDeserializationCallback
        {
            private readonly SortedSet<T> _underlying;
            private readonly T? _min;
            private readonly T? _max;
            // keeps track of whether the count variable is up to date
            // up to date -> _countVersion = _underlying.version
            // not up to date -> _countVersion < _underlying.version
            private int _countVersion;
            // level of the subsets root from the underlying roots.
            // Is up-to date if version = _underlying.version
            private int _rootLevel;
            // these exist for unbounded collections
            // for instance, you could allow this subset to be defined for i > 10. The set will throw if
            // anything <= 10 is added, but there is no upper bound. These features Head(), Tail(), were punted
            // in the spec, and are not available, but the framework is there to make them available at some point.
            private readonly bool _lBoundActive, _uBoundActive;
            // used to see if the count is out of date

            // pal: R32.13. A view of `_underlying`: each operation borrows its recursive tree, and its
            // `root` is the subtree `FindRange` returns (R32.14) whenever its version is the set's.
            [Spec] internal T? SpecMin => _min;
            [Spec] internal T? SpecMax => _max;
            [Spec] internal bool SpecLowerActive => _lBoundActive;
            [Spec] internal bool SpecUpperActive => _uBoundActive;
            [Spec] internal SortedSetLabels<T> ReadLabels => _underlying.SpecLabels;
            [Spec] internal SortedSetSnapshot<T> ReadSnapshot => SortedSetOwnership.Snapshot(_underlying.SpecSnapshot);
            [Spec] internal Seq<T> ReadItems => SpecRangeWalk.Filter<T>(_underlying.SpecComparer,
                _min!, _max!, _lBoundActive, _uBoundActive, _underlying.SpecItems);
            [Spec] public override IComparer<T> SpecComparer => comparer;
            [Spec, EnumerationModel] public override Seq<T> SpecItems => ReadItems;

            // §37. The view's range, and the set's tree whose range root it searches.
            [Spec] internal override Seq<T> SpecRangeLo => SortedSetCount.One(_min!);
            [Spec] internal override Seq<T> SpecRangeHi => SortedSetCount.One(_max!);
            [Spec] internal override bool SpecRangeLa => _lBoundActive;
            [Spec] internal override bool SpecRangeUa => _uBoundActive;
            [Spec] internal override SpecTree<(T, bool)> SpecRangeTree => _underlying.SpecNodes;
            [Spec] internal override IComparer<T> SpecRangeComparer => comparer;
            [Spec] internal override bool SpecRangeReady => SpecCoherent && SpecCountOk && SpecRootOk;
            [Spec] internal override SortedSetObservation<T> SpecIteratorObservation => _underlying.SpecObservation;
            [Spec] internal override SortedSetModel<T> SpecIteratorSnapshot => _underlying.SpecSnapshot;
            [Spec] internal override SpecInt SpecIteratorCapacity => _underlying.SpecCount;
            [Spec] internal override SpecInt SpecIteratorVersion => _underlying.SpecVersion;
            [Spec] internal override Seq<T> SpecIteratorItems => ReadItems;
            [Spec] internal override bool SpecIteratorSourceReady => SpecCoherent;
            [Spec] internal override bool SpecIteratorRootReady => SpecCoherent && SpecRootOk;

            /// <summary>
            /// R32.14. The root is the subtree the range search stops at in the set's tree. §37:
            /// a non-null root is `_rootLevel` below the set's root.
            /// </summary>
            [Spec] internal bool SpecRootOk =>
                SortedSetOwnership.ViewRoot<T>(_underlying.SpecLabels, _underlying.SpecComparer,
                    root, _rootLevel, _min!, _max!, _lBoundActive, _uBoundActive);

            /// <summary>
            /// R32.14. The view shares the set's comparer, and its root is the set's range
            /// subtree whenever its version is the set's (a stale version is re-synchronised by
            /// <see cref="VersionCheckImpl"/>).
            /// </summary>
            [Spec] internal bool SpecCoherent =>
                comparer == _underlying.SpecComparer && Pal.Implies(version == _underlying.SpecVersion, SpecRootOk);

            /// <summary>
            /// R35.19. The cached count is the number of in-range items whenever its version is the
            /// set's (a stale one is re-counted by <see cref="VersionCheckImpl"/>).
            /// </summary>
            [Spec] internal override bool SpecCountOk =>
                Pal.Implies(_countVersion == _underlying.SpecVersion, count == SpecRangeWalk.Filter(_underlying.SpecComparer, _min!, _max!, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length);

#if DEBUG
            internal override bool versionUpToDate()
            {
                return (version == _underlying.version);
            }
#endif

            [Ensures("ReferenceEquals(@this._underlying, Underlying) && Pal.Same(@this._min, Min) && Pal.Same(@this._max, Max)")]
            [Ensures("@this._lBoundActive == lowerBoundActive && @this._uBoundActive == upperBoundActive")]
            [Ensures("@this.version == -1 && @this._countVersion == -1 && @this.SpecRootOk && @this.SpecCoherent")]
            public TreeSubSet(SortedSet<T> Underlying, T? Min, T? Max, bool lowerBoundActive, bool upperBoundActive)
                : base(Underlying.Comparer)
            {
                SortedSetOwnershipProof.ConsumeEmpty<T>();
                _underlying = Underlying;
                _min = Min;
                _max = Max;
                _lBoundActive = lowerBoundActive;
                _uBoundActive = upperBoundActive;
                root = _underlying.FindRange(_min, _max, _lBoundActive, _uBoundActive, out _rootLevel); // root is first element within range
                count = 0;
                version = -1;
                _countVersion = -1;
            }

            // R32.14. Through the view the set is written: in range, as `Add` on it; out of
            // range, `ArgumentOutOfRangeException`. The view's version must not be the one the
            // set's write moves to, or its stale root would pass for current (doc/translation.md
            // §32 Findings).
            [Requires("@this.SpecCoherent && @this._underlying.SpecItems.Length < int.MaxValue && @this.version != SpecWrap.Int32(@this._underlying.SpecVersion + 1)")]
            [Throws(typeof(ArgumentOutOfRangeException), "!SpecSearchTree.InRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item)")]
            [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this._underlying.SpecComparer), Pal.Old(@this._underlying.SpecItems), item) < 0)")]
            [Ensures("Pal.Implies(Result, @this._underlying.SpecItems == SpecTopDown.Inserted(Pal.Old(@this._underlying.SpecComparer), Pal.Old(@this._underlying.SpecItems), item))")]
            [Ensures("Pal.Implies(!Result, @this._underlying.SpecItems == Pal.Old(@this._underlying.SpecItems))")]
            [Ensures("@this.SpecCoherent && @this.version == @this._underlying.SpecVersion && @this.SpecRootOk")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            internal override bool AddIfNotPresent(T item)
            {
                if (!IsWithinRange(item))
                {
                    throw new ArgumentOutOfRangeException(nameof(item));
                }

                bool ret = _underlying.AddIfNotPresent(item);
                VersionCheck();
#if DEBUG
                Debug.Assert(this.versionUpToDate() && root == _underlying.FindRange(_min, _max));
#endif

                return ret;
            }

            [Requires("@this.SpecCoherent")]
            [Ensures("Result == (SpecSearchTree.InRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item) && Pal.KeyIndex(@this._underlying.SpecComparer, @this._underlying.SpecItems, item) >= 0)")]
            [Ensures("@this.SpecCoherent")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            public override bool Contains(T item)
            {
                VersionCheck();
#if DEBUG
                Debug.Assert(versionUpToDate() && root == _underlying.FindRange(_min, _max));
#endif
                return base.Contains(item);
            }

            // R32.14. Through the view an item in range is removed from the set; one out of
            // range is not looked for. The version caveat is `AddIfNotPresent`'s.
            [Requires("@this.SpecCoherent && @this.version != SpecWrap.Int32(@this._underlying.SpecVersion + 1)")]
            [Ensures("Result == (SpecSearchTree.InRange(Pal.Old(@this._underlying.SpecComparer), @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item) && Pal.KeyIndex(Pal.Old(@this._underlying.SpecComparer), Pal.Old(@this._underlying.SpecItems), item) >= 0)")]
            [Ensures("Pal.Implies(SpecSearchTree.InRange(Pal.Old(@this._underlying.SpecComparer), @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item), @this._underlying.SpecItems == SpecTopDownRemove.Removed(Pal.Old(@this._underlying.SpecComparer), Pal.Old(@this._underlying.SpecItems), item))")]
            [Ensures("Pal.Implies(!SpecSearchTree.InRange(Pal.Old(@this._underlying.SpecComparer), @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item), @this._underlying.SpecItems == Pal.Old(@this._underlying.SpecItems))")]
            [Ensures("@this.SpecCoherent")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            internal override bool DoRemove(T item)
            {
                if (!IsWithinRange(item))
                {
                    return false;
                }

                bool ret = _underlying.Remove(item);
                VersionCheck();
#if DEBUG
                Debug.Assert(versionUpToDate() && root == _underlying.FindRange(_min, _max));
#endif
                return ret;
            }

            // pal: R35.19. The view's in-range items are collected by the breadth-first walk
            // and removed from the set one by one.
            [Requires("@this.SpecCoherent && @this.SpecCountOk")]
            [Ensures("@this.count == 0")]
            public override void Clear()
            {
                if (Count == 0)
                {
                    return;
                }

                List<T> toRemove = new List<T>(Count);
                BreadthFirstTreeWalk(n => { Pal.Protocol<(T, bool), bool>(tr => toRemove.Items.Length == tr.Length); toRemove.Add(n.Item); return true; });

                for (int i = toRemove.Count - 1; i >= 0; i--)
                {
                    Pal.Invariant(SortedSetOwnership.Owner(_underlying.root, _underlying.ownershipState, Perm.Full));
                    Pal.Invariant(SortedSetOwnership.Valid(_underlying.root, _underlying.ownershipState,
                        _underlying.comparer, _underlying.count, _underlying.version));
                    Pal.Invariant(i < toRemove.SpecCount);
                    _underlying.Remove(toRemove[i]);
                }

                root = null;
                count = 0;
                version = _underlying.version;
            }

            [Ensures("Result == SpecSearchTree.InRange(@this.comparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item)")]
            [Ensures("@this.root == Pal.Old(@this.root) && @this.comparer == Pal.Old(@this.comparer)")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            internal override bool IsWithinRange(T item)
            {
                int comp = _lBoundActive ? Comparer.Compare(_min, item) : -1;
                if (comp > 0)
                {
                    return false;
                }

                comp = _uBoundActive ? Comparer.Compare(_max, item) : 1;
                return comp >= 0;
            }

            // pal: R35.17. The descent from the view's root to its least (greatest) in-range item.
            [Requires("@this.SpecCoherent")]
            [Ensures("Pal.Same(Result, SpecRangeWalk.FirstOr(SpecRangeWalk.Filter(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems), default(T)))")]
            [Ensures("@this.SpecCoherent && @this.version == @this._underlying.SpecVersion && @this.SpecRootOk")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            internal override T MinInternal
            {
                get
                {
                    VersionCheck();
                    SpecRangeWalk.MinMaxGoal(_underlying.SpecComparer, _underlying.SpecNodes, _min!, _max!, _lBoundActive, _uBoundActive, default(T)!);
                    Ghost<SortedSetLabels<T>> labels = default;
                    Pal.Capture(ref labels, _underlying.SpecLabels);
                    Ghost<Seq<T>> items = default;
                    Pal.Capture(ref items, _underlying.SpecItems);
                    Ghost<SpecInt> checkedVersion = default;
                    Pal.Capture(ref checkedVersion, _underlying.SpecVersion);
                    SortedSetOwnershipProof.RootFacts(labels);
                    SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                    Node? current = root;
                    T? result = default;

                    while (current != null)
                    {
                        Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                        Pal.Invariant(SortedSetOwnership.Owns(labels.Value, Pal.Permission()));
                        Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) &&
                            version == checkedVersion.Value && comparer == Pal.Old(comparer) &&
                            SortedSetOwnership.ViewRoot<T>(labels.Value, comparer, root, _rootLevel, _min!, _max!, _lBoundActive, _uBoundActive) &&
                            (current == null || SortedSetOwnership.Member(labels.Value, current)) &&
                            Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(labels.Value, current))) &&
                            Pal.Same(SpecRangeWalk.FirstOr<T>(SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, false, SpecSearchTree.Keys(SortedSetOwnership.Lookup(labels.Value, current))), result!), SpecRangeWalk.FirstOr<T>(SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive, items.Value), default(T)!)) &&
                            Pal.Implies(Pal.Broke(), Pal.Same(result, SpecRangeWalk.FirstOr<T>(SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive, items.Value), default(T)!))));
                        SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                        SpecRangeWalk.MinStep<T, bool>(comparer, _min!, _max!, _lBoundActive, SortedSetOwnership.Lookup(labels.Value, current), result!);
                        int comp = _lBoundActive ? Comparer.Compare(_min, current!.Item) : -1;
                        if (comp > 0)
                        {
                            current = current!.Right;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        }
                        else
                        {
                            result = current!.Item;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                            if (comp == 0)
                            {
                                break;
                            }
                            SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                            current = current.Left;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        }
                    }

                    return result!;
                }
            }

            // pal: R35.17. The descent from the view's root to its least (greatest) in-range item.
            [Requires("@this.SpecCoherent")]
            [Ensures("Pal.Same(Result, SpecRangeWalk.LastOr(SpecRangeWalk.Filter(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems), default(T)))")]
            [Ensures("@this.SpecCoherent && @this.version == @this._underlying.SpecVersion && @this.SpecRootOk")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            internal override T MaxInternal
            {
                [Rlimit(4)]
                get
                {
                    VersionCheck();
                    SpecRangeWalk.MinMaxGoal(_underlying.SpecComparer, _underlying.SpecNodes, _min!, _max!, _lBoundActive, _uBoundActive, default(T)!);
                    Ghost<SortedSetLabels<T>> labels = default;
                    Pal.Capture(ref labels, _underlying.SpecLabels);
                    Ghost<Seq<T>> items = default;
                    Pal.Capture(ref items, _underlying.SpecItems);
                    Ghost<SpecInt> checkedVersion = default;
                    Pal.Capture(ref checkedVersion, _underlying.SpecVersion);
                    SortedSetOwnershipProof.RootFacts(labels);
                    SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                    Node? current = root;
                    T? result = default;

                    while (current != null)
                    {
                        Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                        Pal.Invariant(SortedSetOwnership.Owns(labels.Value, Pal.Permission()));
                        Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) &&
                            version == checkedVersion.Value && comparer == Pal.Old(comparer) &&
                            SortedSetOwnership.ViewRoot<T>(labels.Value, comparer, root, _rootLevel, _min!, _max!, _lBoundActive, _uBoundActive) &&
                            (current == null || SortedSetOwnership.Member(labels.Value, current)) &&
                            Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(labels.Value, current))) &&
                            Pal.Same(SpecRangeWalk.LastOr<T>(SpecRangeWalk.Filter<T>(comparer, _min!, _max!, false, _uBoundActive, SpecSearchTree.Keys(SortedSetOwnership.Lookup(labels.Value, current))), result!), SpecRangeWalk.LastOr<T>(SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive, items.Value), default(T)!)) &&
                            Pal.Implies(Pal.Broke(), Pal.Same(result, SpecRangeWalk.LastOr<T>(SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive, items.Value), default(T)!))));
                        SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                        SpecRangeWalk.MaxStep<T, bool>(comparer, _min!, _max!, _uBoundActive, SortedSetOwnership.Lookup(labels.Value, current), result!);
                        int comp = _uBoundActive ? Comparer.Compare(_max, current!.Item) : 1;
                        if (comp < 0)
                        {
                            current = current!.Left;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        }
                        else
                        {
                            result = current!.Item;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                            if (comp == 0)
                            {
                                break;
                            }
                            SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                            current = current.Right;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        }
                    }

                    return result!;
                }
            }

            // pal: R35.14. The walk at the view visits the set's items within the range, in
            // order: R27.39's walk over a stack of pointers into the set's region, pruned to the
            // range (`SpecRangeWalk`). Nodes outside the range are passed over towards it.
            [Requires("@this.SpecCoherent && @this._underlying.SpecItems.Length <= Pal.CallBound(action)")]
            [Ensures("SpecWalk.Walked(SpecRangeWalk.Filter(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems), Pal.Trace<(T, bool), bool>(action), Result)")]
            [Ensures("@this.SpecCoherent && @this.version == @this._underlying.SpecVersion && @this.SpecRootOk")]
            [Ensures("Pal.Implies(Pal.Old(@this.SpecCountOk), @this.SpecCountOk)")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            [Rlimit(8)]
            [Fuel(1, 0)]
            [Wrapping]
            internal override bool InOrderTreeWalk([Callback("SortedSetNodeSnapshot<T> snapshot", "SortedSetOwnership.Raw(argument, snapshot, permission)", "SortedSetOwnership.Entry(snapshot)", Bounded = true)] TreeWalkPredicate<T> action)
            {
                VersionCheck();
                SpecRangeWalk.RootFilter(_underlying.SpecComparer, _underlying.SpecNodes, _min!, _max!, _lBoundActive, _uBoundActive);
                Ghost<SortedSetLabels<T>> labels = default;
                Pal.Capture(ref labels, _underlying.SpecLabels);
                Ghost<Seq<T>> items = default;
                Pal.Capture(ref items, _underlying.SpecItems);
                Ghost<Seq<T>> selected = default;
                Pal.Capture(ref selected, SpecRangeWalk.Filter<T>(_underlying.SpecComparer,
                    _min!, _max!, _lBoundActive, _uBoundActive, _underlying.SpecItems));
                Ghost<SortedSetObservation<T>> observation = default;
                Pal.Capture(ref observation, _underlying.SpecObservation);
                SortedSetOwnershipProof.RootFacts(labels);

                if (root == null)
                {
                    return true;
                }

                // The maximum height of a red-black tree is 2*lg(n+1).
                // See page 264 of "Introduction to algorithms" by Thomas H. Cormen
                Stack<Node?> stack = new Stack<Node?>(2 * (int)SortedSet<T>.Log2(count + 1)); // this is not exactly right if count is out of date, but the stack can grow
                Node? current = root;
                SortedSetRangeProof.Empty<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive, stack.Items);
                SortedSetRangeProof.Start<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                    current, stack.Items, selected);
                while (current != null)
                {
                    Pal.Invariant(Pal.Same(_underlying.SpecSnapshot, Pal.Old(_underlying.SpecSnapshot)));
                    Pal.Invariant(Pal.Implies(Pal.Old(SpecCountOk), SpecCountOk));
                    Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, current).Size);
                    Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) &&
                        Pal.Same(ownershipState, Pal.Old(ownershipState)) &&
                        SpecCoherent && version == _underlying.SpecVersion && SpecRootOk &&
                        Pal.Same(_underlying.SpecLabels, labels.Value) && _underlying.SpecItems == items.Value &&
                        this.ReadItems == selected.Value);
                    Pal.Invariant((current == null || SortedSetOwnership.Member(labels.Value, current)) &&
                        Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(labels.Value, current))) &&
                        SortedSetWalk.Walkable(labels.Value, stack.Items) &&
                        SortedSetRange.Walkable<T>(labels.Value, comparer, _min!, _max!, _lBoundActive, _uBoundActive, stack.Items) &&
                        SpecWalk.Keys(false, SortedSetOwnership.Lookup(labels.Value, current)).Length +
                            SortedSetWalk.Pending(false, labels.Value, stack.Items).Length <= items.Value.Length &&
                        Pal.Trace<(T, bool), bool>(action).Length == 0 &&
                        SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                            Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(labels.Value, current)),
                                SortedSetWalk.Pending(false, labels.Value, stack.Items))) == selected.Value);
                    SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                    SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                    var item = current!.Item;
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                    SortedSetOwnershipProof.EndSet(labels, Pal.Permission());
                    if (IsWithinRange(item))
                    {
                        SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                        SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                        SortedSetWalkProof.Descend(false, labels, stack.Items, current);
                        SortedSetRangeProof.Push<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive, stack.Items, current);
                        stack.Push(current);
                        current = current.Left;
                        SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                    }
                    else
                    {
                        SortedSetStateProof.NodeFacts<T>(observation, labels, current, Pal.Permission());
                        SortedSetStateProof.Open<T>(observation, current, Pal.Permission());
                        if (_lBoundActive && Comparer.Compare(_min, current.Item) > 0)
                        {
                            SortedSetStateProof.Close<T>(observation, current, Pal.Permission());
                            SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                            SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                            SortedSetRangeProof.SkipRight<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                                current, SortedSetWalk.Pending(false, labels.Value, stack.Items));
                            current = current.Right;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        }
                        else
                        {
                            SortedSetStateProof.Close<T>(observation, current, Pal.Permission());
                            SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                            SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                            SortedSetRangeProof.SkipLeft<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                                current, SortedSetWalk.Pending(false, labels.Value, stack.Items));
                            current = current.Left;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        }
                    }
                }

                while (stack.Count != 0)
                {
                    Pal.Invariant(Pal.Same(_underlying.SpecSnapshot, Pal.Old(_underlying.SpecSnapshot)));
                    Pal.Invariant(Pal.Implies(Pal.Old(SpecCountOk), SpecCountOk));
                    Pal.Decreases(selected.Value.Length - Pal.Trace<(T, bool), bool>(action).Length);
                    Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) &&
                        Pal.Same(ownershipState, Pal.Old(ownershipState)) &&
                        SpecCoherent && version == _underlying.SpecVersion && SpecRootOk &&
                        Pal.Same(_underlying.SpecLabels, labels.Value) && _underlying.SpecItems == items.Value &&
                        this.ReadItems == selected.Value);
                    Pal.Invariant(SortedSetWalk.Walkable(labels.Value, stack.Items) &&
                        SortedSetRange.Walkable<T>(labels.Value, comparer, _min!, _max!, _lBoundActive, _uBoundActive, stack.Items) &&
                        SortedSetWalk.Pending(false, labels.Value, stack.Items).Length <= items.Value.Length &&
                        0 <= Pal.Trace<(T, bool), bool>(action).Length &&
                        Pal.Trace<(T, bool), bool>(action).Length <= selected.Value.Length &&
                        Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() &&
                            SpecWalk.Walked(selected.Value, Pal.Trace<(T, bool), bool>(action), false)) &&
                        Pal.Implies(!Pal.Returned(), SpecWalk.Visited(selected.Value, Pal.Trace<(T, bool), bool>(action)) &&
                            SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                                SortedSetWalk.Pending(false, labels.Value, stack.Items)) ==
                                Pal.Slice(selected.Value, Pal.Trace<(T, bool), bool>(action).Length, selected.Value.Length)));
                    Pal.Assert(!Pal.Returned());
                    Pal.Assert(stack.SpecCount != 0);
                    Pal.Assert(stack.SpecCount == stack.Items.Length);
                    Pal.Assert(stack.Items.Length > 0);
                    SortedSetRangeProof.PopAt<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                        stack.Items, selected, (SpecInt)Pal.Trace<(T, bool), bool>(action).Length);
                    current = stack.Pop();
                    Pal.Assert(Pal.Trace<(T, bool), bool>(action).Length < selected.Value.Length);
                    SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                    SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                    Ghost<Seq<((T, bool), bool)>> before = default;
                    Pal.Capture(ref before, Pal.Trace<(T, bool), bool>(action));
                    if (!action(current!))
                    {
                        SortedSetWalkProof.TraceStep(selected, before, Pal.Trace<(T, bool), bool>(action), false);
                        SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        return false;
                    }
                    else
                    {
                        SortedSetWalkProof.TraceStep(selected, before, Pal.Trace<(T, bool), bool>(action), true);
                        SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                    }
                    SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());

                    Node? node = current!.Right;
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                    SortedSetOwnershipProof.EndSet(labels, Pal.Permission());
                    while (node != null)
                    {
                        Pal.Invariant(Pal.Same(_underlying.SpecSnapshot, Pal.Old(_underlying.SpecSnapshot)));
                        Pal.Invariant(Pal.Implies(Pal.Old(SpecCountOk), SpecCountOk));
                        Pal.Decreases(SortedSetOwnership.Lookup(labels.Value, node).Size);
                        Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) &&
                            Pal.Same(ownershipState, Pal.Old(ownershipState)) &&
                            SpecCoherent && version == _underlying.SpecVersion && SpecRootOk &&
                            Pal.Same(_underlying.SpecLabels, labels.Value) && _underlying.SpecItems == items.Value &&
                            this.ReadItems == selected.Value);
                        Pal.Invariant((node == null || SortedSetOwnership.Member(labels.Value, node)) &&
                            Pal.StrictlySorted(comparer, SpecSearchTree.Keys(SortedSetOwnership.Lookup(labels.Value, node))) &&
                            SortedSetWalk.Walkable(labels.Value, stack.Items) &&
                            SortedSetRange.Walkable<T>(labels.Value, comparer, _min!, _max!, _lBoundActive, _uBoundActive, stack.Items) &&
                            SpecWalk.Keys(false, SortedSetOwnership.Lookup(labels.Value, node)).Length +
                                SortedSetWalk.Pending(false, labels.Value, stack.Items).Length <= items.Value.Length &&
                            0 < Pal.Trace<(T, bool), bool>(action).Length &&
                            Pal.Trace<(T, bool), bool>(action).Length <= selected.Value.Length &&
                            SpecWalk.Visited(selected.Value, Pal.Trace<(T, bool), bool>(action)) &&
                            SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                                Pal.Concat(SpecWalk.Keys(false, SortedSetOwnership.Lookup(labels.Value, node)),
                                    SortedSetWalk.Pending(false, labels.Value, stack.Items))) ==
                                    Pal.Slice(selected.Value, Pal.Trace<(T, bool), bool>(action).Length, selected.Value.Length));
                        SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                        SortedSetOwnershipProof.OpenRead(labels, node, Pal.Permission());
                        var item = node!.Item;
                        SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        SortedSetOwnershipProof.EndSet(labels, Pal.Permission());
                        if (IsWithinRange(item))
                        {
                            SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                            SortedSetOwnershipProof.OpenRead(labels, node, Pal.Permission());
                            SortedSetWalkProof.Descend(false, labels, stack.Items, node);
                            SortedSetRangeProof.Push<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive, stack.Items, node);
                            stack.Push(node);
                            node = node.Left;
                            SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        }
                        else
                        {
                            SortedSetStateProof.NodeFacts<T>(observation, labels, node, Pal.Permission());
                            SortedSetStateProof.Open<T>(observation, node, Pal.Permission());
                            if (_lBoundActive && Comparer.Compare(_min, node.Item) > 0)
                            {
                                SortedSetStateProof.Close<T>(observation, node, Pal.Permission());
                                SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                                SortedSetOwnershipProof.OpenRead(labels, node, Pal.Permission());
                                SortedSetRangeProof.SkipRight<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                                    node, SortedSetWalk.Pending(false, labels.Value, stack.Items));
                                node = node.Right;
                                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                            }
                            else
                            {
                                SortedSetStateProof.Close<T>(observation, node, Pal.Permission());
                                SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                                SortedSetOwnershipProof.OpenRead(labels, node, Pal.Permission());
                                SortedSetRangeProof.SkipLeft<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                                    node, SortedSetWalk.Pending(false, labels.Value, stack.Items));
                                node = node.Left;
                                SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                            }
                        }
                    }
                }
                return true;
            }

            // pal: R35.14. The breadth-first walk at the view calls `action` on the set's items
            // within the range, level by level, and stops at the first false: R27.40's walk over
            // a queue of pointers into the set's region, which queues a child only if the range
            // may reach into it (`SpecRangeWalk.BfNext`). Nodes outside the range are not called on.
            [Requires("@this.SpecCoherent && @this._underlying.SpecItems.Length <= Pal.CallBound(action)")]
            [Ensures("SpecWalk.BfWalked(SpecRangeWalk.Filter(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems), Pal.Trace<(T, bool), bool>(action), Result)")]
            [Ensures("@this.SpecCoherent && @this.version == @this._underlying.SpecVersion && @this.SpecRootOk")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            [Rlimit(8), Fuel(1, 0)]
            [Wrapping]
            internal override bool BreadthFirstTreeWalk([Callback("SortedSetNodeSnapshot<T> snapshot", "SortedSetOwnership.Raw(argument, snapshot, permission)", "SortedSetOwnership.Entry(snapshot)", Bounded = true)] TreeWalkPredicate<T> action)
            {
                VersionCheck();
                SpecRangeWalk.RootFilter(_underlying.SpecComparer, _underlying.SpecNodes, _min!, _max!, _lBoundActive, _uBoundActive);
                Ghost<SortedSetSnapshot<T>> snapshot = default;
                Pal.Capture(ref snapshot, SortedSetOwnership.Snapshot(_underlying.SpecSnapshot));
                Ghost<SortedSetReadHandle<T>> lease = default;
                Pal.Capture(ref lease, SortedSetOwnership.ViewHandle(this, snapshot.Value));
                SortedSetOwnership.ViewHandleFacts(this, snapshot.Value);
                Ghost<SortedSetLabels<T>> labels = default;
                Pal.Capture(ref labels, _underlying.SpecLabels);
                Ghost<Seq<T>> items = default;
                Pal.Capture(ref items, _underlying.SpecItems);
                Ghost<Seq<T>> selected = default;
                Pal.Capture(ref selected, SpecRangeWalk.Filter<T>(_underlying.SpecComparer,
                    _min!, _max!, _lBoundActive, _uBoundActive, _underlying.SpecItems));
                SortedSetOwnershipProof.RootFacts(labels);

                if (root == null)
                {
                    return true;
                }

                Queue<Node?> processQueue = new Queue<Node?>();
                processQueue.Enqueue(root);
                SortedSetRangeBreadthProof.Start<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                    root, processQueue.Items, selected, Pal.Trace<(T, bool), bool>(action));
                Node? current;

                while (processQueue.Count != 0)
                {
                    Pal.Decreases(SortedSetBreadth.Pending(labels.Value, processQueue.Items).Length);
                    Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) &&
                        Pal.Same(SortedSetOwnership.Snapshot(_underlying.SpecSnapshot), snapshot.Value) &&
                        SortedSetOwnership.HandleMatchesView(lease.Value, this, snapshot.Value) &&
                        Pal.Same(ownershipState, Pal.Old(ownershipState)) &&
                        SpecCoherent && version == _underlying.SpecVersion && SpecRootOk &&
                        Pal.Same(_underlying.SpecLabels, labels.Value) && _underlying.SpecItems == items.Value &&
                        this.ReadItems == selected.Value &&
                        SortedSetWalk.Walkable(labels.Value, processQueue.Items) &&
                        SortedSetRangeBreadth.Queue(labels.Value, comparer, processQueue.Items) &&
                        SortedSetBreadth.Pending(labels.Value, processQueue.Items).Length <= items.Value.Length &&
                        Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() &&
                            SpecWalk.BfWalked(selected.Value, Pal.Trace<(T, bool), bool>(action), false)) &&
                        Pal.Implies(!Pal.Returned(), SpecWalk.BfVisited(selected.Value, Pal.Trace<(T, bool), bool>(action),
                            SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                                SortedSetBreadth.Pending(labels.Value, processQueue.Items)))));
                    Pal.Assert(!Pal.Returned());
                    Pal.Assert(processQueue.SpecCount != 0);
                    Pal.Assert(processQueue.Items.Length > 0);
                    Ghost<Seq<Node?>> q0 = default;
                    Pal.Capture(ref q0, processQueue.Items);
                    SortedSetRangeBreadthProof.Dequeue<T>(labels, comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                        q0, selected, Pal.Trace<(T, bool), bool>(action));
                    current = processQueue.Dequeue();
                    SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                    SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                    var item = current!.Item;
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                    SortedSetOwnershipProof.EndSet(labels, Pal.Permission());
                    bool inRange = IsWithinRange(item);
                    SortedSetOwnershipProof.ReadSet(labels, Pal.Permission());
                    SortedSetOwnershipProof.OpenRead(labels, current, Pal.Permission());
                    SortedSetOwnershipProof.WindowToHandle(lease, labels, current, Pal.Permission());
                    if (inRange && !action(current!))
                    {
                        SortedSetOwnershipProof.WindowFromHandle(_underlying,
                            SortedSetOwnership.Snapshot(Pal.Old(_underlying.SpecSnapshot)),
                            lease, labels, current, Pal.Permission());
                        SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                        SortedSetOwnershipProof.EndSet(labels, Pal.Permission());
                        return false;
                    }
                    Pal.Join(SortedSetOwnership.HandleOrClosed(_underlying,
                        SortedSetOwnership.Snapshot(Pal.Old(_underlying.SpecSnapshot)),
                        lease.Value, labels.Value, current, Pal.Permission(), Pal.Returned()));
                    Pal.Join(processQueue.Items == Pal.Slice(q0.Value, 1, q0.Value.Length));
                    Pal.Join(current == q0.Value[0]);
                    Pal.Join(Pal.Implies(Pal.Returned(), !Pal.Result<bool>() &&
                        SpecWalk.BfWalked(selected.Value, Pal.Trace<(T, bool), bool>(action), false)));
                    Pal.Join(Pal.Implies(!Pal.Returned(), SpecWalk.BfVisited(selected.Value, Pal.Trace<(T, bool), bool>(action),
                        SpecRangeWalk.Filter<T>(comparer, _min!, _max!, _lBoundActive, _uBoundActive,
                            SortedSetBreadth.Pending(labels.Value,
                                SortedSetRangeBreadth.Next<T>(labels.Value, comparer, _min!, _max!, _lBoundActive, _uBoundActive, q0.Value))))));
                    SortedSetOwnershipProof.ContinueHandle(_underlying,
                        SortedSetOwnership.Snapshot(Pal.Old(_underlying.SpecSnapshot)),
                        lease, labels, current, Pal.Permission(), Pal.Returned());
                    Pal.Assert(processQueue.SpecCount < int.MaxValue);
                    if (current!.Left != null && (!_lBoundActive || Comparer.Compare(_min, current!.Item) < 0))
                    {
                        processQueue.Enqueue(current!.Left);
                    }
                    Pal.Join(SortedSetOwnership.HandleOrClosed(_underlying,
                        SortedSetOwnership.Snapshot(Pal.Old(_underlying.SpecSnapshot)),
                        lease.Value, labels.Value, current, Pal.Permission(), false));
                    Pal.Join(processQueue.Items == (SortedSetRangeBreadth.TakeLeft<T>(labels.Value, comparer, _min!, _lBoundActive, current)
                        ? Pal.Snoc(Pal.Slice(q0.Value, 1, q0.Value.Length), SortedSetWalk.Near(false, labels.Value, current))
                        : Pal.Slice(q0.Value, 1, q0.Value.Length)));
                    SortedSetOwnershipProof.ContinueHandle(_underlying,
                        SortedSetOwnership.Snapshot(Pal.Old(_underlying.SpecSnapshot)),
                        lease, labels, current, Pal.Permission(), false);
                    Ghost<Seq<Node?>> q1 = default;
                    Pal.Capture(ref q1, processQueue.Items);
                    Pal.Assert(processQueue.SpecCount < int.MaxValue);
                    if (current!.Right != null && (!_uBoundActive || Comparer.Compare(_max, current!.Item) > 0))
                    {
                        processQueue.Enqueue(current!.Right);
                    }
                    Pal.Join(SortedSetOwnership.HandleOrClosed(_underlying,
                        SortedSetOwnership.Snapshot(Pal.Old(_underlying.SpecSnapshot)),
                        lease.Value, labels.Value, current, Pal.Permission(), false));
                    Pal.Join(processQueue.Items == (SortedSetRangeBreadth.TakeRight<T>(labels.Value, comparer, _min!, _max!, _uBoundActive, current)
                        ? Pal.Snoc(q1.Value, SortedSetWalk.Far(false, labels.Value, current))
                        : q1.Value));
                    SortedSetOwnershipProof.ContinueHandle(_underlying,
                        SortedSetOwnership.Snapshot(Pal.Old(_underlying.SpecSnapshot)),
                        lease, labels, current, Pal.Permission(), false);
                    Pal.Assert(processQueue.Items == SortedSetRangeBreadth.Next<T>(labels.Value, comparer,
                        _min!, _max!, _lBoundActive, _uBoundActive, q0.Value));
                    SortedSetOwnershipProof.WindowFromHandle(_underlying,
                        SortedSetOwnership.Snapshot(Pal.Old(_underlying.SpecSnapshot)),
                        lease, labels, current, Pal.Permission());
                    SortedSetOwnershipProof.CloseRead(labels, Pal.Permission());
                    SortedSetOwnershipProof.EndSet(labels, Pal.Permission());
                }
                return true;
            }

            [Requires("@this.SpecCoherent")]
            [Ensures("(Result != null) == (SpecSearchTree.InRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item) && Pal.KeyIndex(@this._underlying.SpecComparer, @this._underlying.SpecItems, item) >= 0)")]
            [Ensures("Result == null || SortedSetOwnership.Member(@this._underlying.SpecLabels, Result) && Pal.Compare(@this._underlying.SpecComparer, SpecSearchTree.RootKey(SortedSetOwnership.Lookup(@this._underlying.SpecLabels, Result), item), item) == 0")]
            [Ensures("@this.SpecCoherent")]
            [Ensures("Pal.Implies(Pal.Old(@this.SpecCountOk), @this.SpecCountOk)")]
            [Ensures("Pal.Implies(Pal.Old(@this.SpecRootOk), @this.SpecRootOk)")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            internal override SortedSet<T>.Node? FindNode(T item)
            {
                if (!IsWithinRange(item))
                {
                    return null;
                }

                VersionCheck();
#if DEBUG
                Debug.Assert(this.versionUpToDate() && root == _underlying.FindRange(_min, _max));
#endif
                return base.FindNode(item);
            }

            /// <summary>
            /// Checks whether this subset is out of date, and updates it if necessary.
            /// </summary>
            /// <param name="updateCount">Updates the count variable if necessary.</param>
            internal override void VersionCheck([Specialize] bool updateCount = false) => VersionCheckImpl(updateCount);

            // pal: R35.18. Translated at each constant `updateCount` its callers pass: the
            // re-count calls the view's walk, which calls `VersionCheck()`, so without it the
            // two would call each other. R35.19: the lambda counts in a copy of `count`.
            [Requires("@this.SpecCoherent && Pal.Implies(updateCount, @this.SpecCountOk)")]
            [Ensures("@this.SpecCoherent && @this.version == @this._underlying.SpecVersion && @this.SpecRootOk")]
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            [Ensures("Pal.Implies(updateCount, @this.count == SpecRangeWalk.Filter(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, @this._underlying.SpecItems).Length && @this._countVersion == @this._underlying.SpecVersion)")]
            [Ensures("Pal.Implies(!updateCount, @this.count == Pal.Old(@this.count) && @this._countVersion == Pal.Old(@this._countVersion))")]
            private void VersionCheckImpl([Specialize] bool updateCount)
            {
                Debug.Assert(_underlying != null);
                if (version != _underlying.version)
                {
                    root = _underlying.FindRange(_min, _max, _lBoundActive, _uBoundActive, out _rootLevel);
                    version = _underlying.version;
                }

                if (updateCount && _countVersion != _underlying.version)
                {
                    count = 0;
                    InOrderTreeWalk(n => { Pal.Protocol<(T, bool), bool>(tr => count == tr.Length && SpecRangeWalk.AllTrue(tr)); count++; return true; });
                    _countVersion = _underlying.version;
                }
            }

            /// <summary>
            /// Returns the number of elements <c>count</c> of the parent set.
            /// </summary>
            internal override int TotalCount()
            {
                Debug.Assert(_underlying != null);
                return _underlying.Count;
            }

            internal override int GetApproximateMaxHeight()
            {
                SortedSetCount.RangeRootHeight(_underlying.SpecComparer, _underlying.SpecNodes, _min!, _max!, _lBoundActive, _uBoundActive);
                    SortedSetOwnershipProof.RootFacts<T>(_underlying.SpecLabels);
                    Pal.Assert(SortedSetOwnership.Lookup(_underlying.SpecLabels, root).IsLeaf ||
                        SortedSetOwnership.Lookup(_underlying.SpecLabels, root).Height + _rootLevel <= _underlying.SpecNodes.Height);
                // pal: R23.12. `Math.Max` of effect-free arguments: the call is bound first.
                int underlyingHeight = _underlying.GetApproximateMaxHeight();
                return Math.Max(underlyingHeight - _rootLevel, 0);
            }

            // This passes functionality down to the underlying tree, clipping edges if necessary
            // There's nothing gained by having a nested subset. May as well draw it from the base
            // Cannot increase the bounds of the subset, can only decrease it
            public override SortedSet<T> GetViewBetween(T? lowerValue, T? upperValue)
            {
                if (_lBoundActive && Comparer.Compare(_min, lowerValue) > 0)
                {
                    throw new ArgumentOutOfRangeException(nameof(lowerValue));
                }
                if (_uBoundActive && Comparer.Compare(_max, upperValue) < 0)
                {
                    throw new ArgumentOutOfRangeException(nameof(upperValue));
                }
                return (TreeSubSet)_underlying.GetViewBetween(lowerValue, upperValue);
            }

#if DEBUG
            internal override void IntersectWithEnumerable(IEnumerable<T> other)
            {
                base.IntersectWithEnumerable(other);
                Debug.Assert(versionUpToDate() && root == _underlying.FindRange(_min, _max));
            }
#endif

            void ISerializable.GetObjectData(SerializationInfo info, StreamingContext context) => GetObjectData(info, context);

            protected override void GetObjectData(SerializationInfo info, StreamingContext context)
            {
                throw new PlatformNotSupportedException();
            }

            void IDeserializationCallback.OnDeserialization(object? sender)
            {
                throw new PlatformNotSupportedException();
            }

            protected override void OnDeserialization(object? sender) => throw new PlatformNotSupportedException();
        }
    }
}
