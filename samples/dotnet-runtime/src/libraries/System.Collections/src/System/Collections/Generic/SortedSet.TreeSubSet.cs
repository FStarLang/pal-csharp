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

            // pal: R32.13. A view of `_underlying`: its record borrows the set's region, and its
            // `root` is the subtree `FindRange` returns (R32.14) whenever its version is the set's.
            [Spec] internal T? SpecMin => _min;
            [Spec] internal T? SpecMax => _max;
            [Spec] internal bool SpecLowerActive => _lBoundActive;
            [Spec] internal bool SpecUpperActive => _uBoundActive;

            // §37. The view's range, and the set's tree whose range root it searches.
            [Spec] internal override Seq<T> SpecRangeLo => SortedSetCount.One(_min);
            [Spec] internal override Seq<T> SpecRangeHi => SortedSetCount.One(_max);
            [Spec] internal override bool SpecRangeLa => _lBoundActive;
            [Spec] internal override bool SpecRangeUa => _uBoundActive;
            [Spec] internal override SpecTree<(T, bool)> SpecRangeTree => _underlying.SpecNodes;
            [Spec] internal override IComparer<T> SpecRangeComparer => comparer;

            /// <summary>
            /// R32.14. The root is the subtree the range search stops at in the set's tree. §37:
            /// a non-null root is `_rootLevel` below the set's root.
            /// </summary>
            [Spec] internal bool SpecRootOk =>
                (root == null || Pal.Unshared(root)) &&
                Pal.Tree<(T, bool)>(root) == SpecSearchTree.RangeRoot(_underlying.SpecComparer, _underlying.SpecNodes, _min, _max, _lBoundActive, _uBoundActive) &&
                0 <= _rootLevel &&
                (root == null || _rootLevel == SortedSetCount.RangeDepth(_underlying.SpecComparer, _underlying.SpecNodes, _min, _max, _lBoundActive, _uBoundActive));

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
            [Spec] internal bool SpecCountOk =>
                Pal.Implies(_countVersion == _underlying.SpecVersion, count == SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length);

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
                    SpecRangeWalk.MinMaxGoal(_underlying.SpecComparer, _underlying.SpecNodes, _min, _max, _lBoundActive, _uBoundActive, default(T));
                    Node? current = root;
                    T? result = default;

                    while (current != null)
                    {
                        Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                        Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) && SpecCoherent && version == _underlying.SpecVersion && SpecRootOk && comparer == _underlying.SpecComparer && Pal.WellFormed(current) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(current))) &&
                                      Pal.Same(SpecRangeWalk.FirstOr(SpecRangeWalk.Filter(comparer, _min, _max, _lBoundActive, false, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(current))), result), SpecRangeWalk.FirstOr(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), default(T))) &&
                                      Pal.Implies(Pal.Broke(), Pal.Same(result, SpecRangeWalk.FirstOr(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), default(T)))));
                        SpecRangeWalk.MinStep(comparer, _min, _max, _lBoundActive, Pal.Tree<(T, bool)>(current), result);
                        int comp = _lBoundActive ? Comparer.Compare(_min, current.Item) : -1;
                        if (comp > 0)
                        {
                            current = current.Right;
                        }
                        else
                        {
                            result = current.Item;
                            if (comp == 0)
                            {
                                break;
                            }
                            current = current.Left;
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
                    SpecRangeWalk.MinMaxGoal(_underlying.SpecComparer, _underlying.SpecNodes, _min, _max, _lBoundActive, _uBoundActive, default(T));
                    Node? current = root;
                    T? result = default;

                    while (current != null)
                    {
                        Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                        Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) && SpecCoherent && version == _underlying.SpecVersion && SpecRootOk && comparer == _underlying.SpecComparer && Pal.WellFormed(current) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(current))) &&
                                      Pal.Same(SpecRangeWalk.LastOr(SpecRangeWalk.Filter(comparer, _min, _max, false, _uBoundActive, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(current))), result), SpecRangeWalk.LastOr(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), default(T))) &&
                                      Pal.Implies(Pal.Broke(), Pal.Same(result, SpecRangeWalk.LastOr(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), default(T)))));
                        SpecRangeWalk.MaxStep(comparer, _min, _max, _uBoundActive, Pal.Tree<(T, bool)>(current), result);
                        int comp = _uBoundActive ? Comparer.Compare(_max, current.Item) : 1;
                        if (comp < 0)
                        {
                            current = current.Left;
                        }
                        else
                        {
                            result = current.Item;
                            if (comp == 0)
                            {
                                break;
                            }
                            current = current.Right;
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
            [Ensures("Pal.Same(@this._min, Pal.Old(@this._min)) && Pal.Same(@this._max, Pal.Old(@this._max))")]
            [Rlimit(16)]
            [Wrapping]
            internal override bool InOrderTreeWalk([Callback(Bounded = true)] TreeWalkPredicate<T> action)
            {
                VersionCheck();
                SpecRangeWalk.RootFilter(_underlying.SpecComparer, _underlying.SpecNodes, _min, _max, _lBoundActive, _uBoundActive);

                if (root == null)
                {
                    return true;
                }

                // The maximum height of a red-black tree is 2*lg(n+1).
                // See page 264 of "Introduction to algorithms" by Thomas H. Cormen
                Stack<Node> stack = new Stack<Node>(2 * (int)SortedSet<T>.Log2(count + 1)); // this is not exactly right if count is out of date, but the stack can grow
                Node? current = root;
                SpecRangeWalk.Empty<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, stack.Items);
                while (current != null)
                {
                    Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
                    Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) && SpecCoherent && version == _underlying.SpecVersion && SpecRootOk && Pal.WellFormed(current) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(current))) && SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), stack.Items) && SpecRangeWalk.Walkable<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, stack.Items) && comparer == _underlying.SpecComparer && _underlying.SpecItems.Length <= int.MaxValue && SpecWalk.Keys(false, Pal.Tree<(T, bool)>(current)).Length + SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items).Length <= _underlying.SpecItems.Length &&
                                  Pal.Trace<(T, bool), bool>(action).Length == 0 &&
                                  SpecRangeWalk.Filter(comparer, _min, _max, _lBoundActive, _uBoundActive, Pal.Concat(SpecWalk.Keys(false, Pal.Tree<(T, bool)>(current)), SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items))) == Pal.Slice(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), 0, SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length));
                    if (IsWithinRange(current.Item))
                    {
                        SpecWalk.Descend<Node, T>(false, Pal.Heap<Node>(), stack.Items, current);
                        SpecRangeWalk.Push<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, stack.Items, current);
                        stack.Push(current);
                        current = current.Left;
                    }
                    else if (_lBoundActive && Comparer.Compare(_min, current.Item) > 0)
                    {
                        SpecRangeWalk.SkipRight<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, current, SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items));
                        current = current.Right;
                    }
                    else
                    {
                        SpecRangeWalk.SkipLeft<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, current, SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items));
                        current = current.Left;
                    }
                }

                while (stack.Count != 0)
                {
                    Pal.Decreases(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length - Pal.Trace<(T, bool), bool>(action).Length);
                    Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) && SpecCoherent && version == _underlying.SpecVersion && SpecRootOk && SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), stack.Items) && SpecRangeWalk.Walkable<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, stack.Items) &&
                                  comparer == _underlying.SpecComparer && _underlying.SpecItems.Length <= int.MaxValue &&
                                  SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items).Length <= _underlying.SpecItems.Length &&
                                  0 <= Pal.Trace<(T, bool), bool>(action).Length && Pal.Trace<(T, bool), bool>(action).Length <= SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length &&
                                  Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() && SpecWalk.Walked(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action), false)) &&
                                  Pal.Implies(!Pal.Returned(), SpecWalk.Visited(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action)) &&
                                        SpecRangeWalk.Filter(comparer, _min, _max, _lBoundActive, _uBoundActive, SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items)) == Pal.Slice(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action).Length, SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length)));
                    Pal.Assert(stack.Items.Length > 0);
                    SpecRangeWalk.PopAt<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, stack.Items, SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action).Length);
                    current = stack.Pop();
                    Pal.Assert(Pal.Trace<(T, bool), bool>(action).Length < SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length);
                    if (!action(current))
                    {
                        return false;
                    }

                    Node? node = current.Right;
                    while (node != null)
                    {
                        Pal.Decreases(Pal.Tree<(T, bool)>(node).Size);
                        Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) && SpecCoherent && version == _underlying.SpecVersion && SpecRootOk && Pal.WellFormed(node) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(Pal.Tree<(T, bool)>(node))) && SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), stack.Items) && SpecRangeWalk.Walkable<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, stack.Items) && comparer == _underlying.SpecComparer && _underlying.SpecItems.Length <= int.MaxValue && SpecWalk.Keys(false, Pal.Tree<(T, bool)>(node)).Length + SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items).Length <= _underlying.SpecItems.Length &&
                                      0 < Pal.Trace<(T, bool), bool>(action).Length && Pal.Trace<(T, bool), bool>(action).Length <= SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length && SpecWalk.Visited(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action)) &&
                                      SpecRangeWalk.Filter(comparer, _min, _max, _lBoundActive, _uBoundActive, Pal.Concat(SpecWalk.Keys(false, Pal.Tree<(T, bool)>(node)), SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items))) == Pal.Slice(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action).Length, SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems).Length));
                        if (IsWithinRange(node.Item))
                        {
                            SpecWalk.Descend<Node, T>(false, Pal.Heap<Node>(), stack.Items, node);
                            SpecRangeWalk.Push<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, stack.Items, node);
                            stack.Push(node);
                            node = node.Left;
                        }
                        else if (_lBoundActive && Comparer.Compare(_min, node.Item) > 0)
                        {
                            SpecRangeWalk.SkipRight<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, node, SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items));
                            node = node.Right;
                        }
                        else
                        {
                            SpecRangeWalk.SkipLeft<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, node, SpecWalk.Pending<Node, T>(false, Pal.Heap<Node>(), stack.Items));
                            node = node.Left;
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
            [Rlimit(16)]
            [Wrapping]
            internal override bool BreadthFirstTreeWalk([Callback(Bounded = true)] TreeWalkPredicate<T> action)
            {
                VersionCheck();
                SpecRangeWalk.RootFilter(_underlying.SpecComparer, _underlying.SpecNodes, _min, _max, _lBoundActive, _uBoundActive);

                if (root == null)
                {
                    return true;
                }

                Queue<Node> processQueue = new Queue<Node>();
                processQueue.Enqueue(root);
                SpecRangeWalk.BfStart<Node, T, bool>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, processQueue.Items, SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action));
                Node current;

                while (processQueue.Count != 0)
                {
                    Pal.Decreases(SpecWalk.BfPending<Node, T>(Pal.Heap<Node>(), processQueue.Items).Length);
                    Pal.Invariant(Pal.Same(_min, Pal.Old(_min)) && Pal.Same(_max, Pal.Old(_max)) && SpecCoherent && version == _underlying.SpecVersion && SpecRootOk && SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), processQueue.Items) && SpecRangeWalk.Queue<Node, T>(Pal.Heap<Node>(), comparer, processQueue.Items) &&
                                  comparer == _underlying.SpecComparer && _underlying.SpecItems.Length <= int.MaxValue &&
                                  SpecWalk.BfPending<Node, T>(Pal.Heap<Node>(), processQueue.Items).Length <= _underlying.SpecItems.Length &&
                                  Pal.Implies(Pal.Returned(), !Pal.ReturnValue<bool>() && SpecWalk.BfWalked(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action), false)) &&
                                  Pal.Implies(!Pal.Returned(), SpecWalk.BfVisited(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action), SpecRangeWalk.Filter(comparer, _min, _max, _lBoundActive, _uBoundActive, SpecWalk.BfPending<Node, T>(Pal.Heap<Node>(), processQueue.Items)))));
                    Ghost<Seq<Node>> q0 = processQueue.Items;
                    SpecRangeWalk.BfDequeue<Node, T, bool>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, q0.Value, SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action));
                    current = processQueue.Dequeue();
                    if (IsWithinRange(current.Item) && !action(current))
                    {
                        return false;
                    }
                    Pal.Join(current == q0.Value[0]);
                    Pal.Join(Pal.Implies(Pal.Returned(), !Pal.Result<bool>() && SpecWalk.BfWalked(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action), false)));
                    Pal.Join(Pal.Implies(!Pal.Returned(), SpecWalk.BfVisited(SpecRangeWalk.Filter(_underlying.SpecComparer, _min, _max, _lBoundActive, _uBoundActive, _underlying.SpecItems), Pal.Trace<(T, bool), bool>(action), SpecRangeWalk.Filter(comparer, _min, _max, _lBoundActive, _uBoundActive, SpecWalk.BfPending<Node, T>(Pal.Heap<Node>(), SpecRangeWalk.BfNext<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, q0.Value))))));
                    Pal.Assert(processQueue.SpecCount < int.MaxValue);
                    if (current.Left != null && (!_lBoundActive || Comparer.Compare(_min, current.Item) < 0))
                    {
                        processQueue.Enqueue(current.Left);
                    }
                    Pal.Join(processQueue.Items == (Pal.LeftOf(current) != null && (!_lBoundActive || Pal.Compare(comparer, _min, SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(current), _min)) < 0)
                        ? Pal.Snoc(Pal.Slice(q0.Value, 1, q0.Value.Length), Pal.LeftOf(current))
                        : Pal.Slice(q0.Value, 1, q0.Value.Length)));
                    Ghost<Seq<Node>> q1 = processQueue.Items;
                    Pal.Assert(processQueue.SpecCount < int.MaxValue);
                    if (current.Right != null && (!_uBoundActive || Comparer.Compare(_max, current.Item) > 0))
                    {
                        processQueue.Enqueue(current.Right);
                    }
                    Pal.Join(processQueue.Items == (Pal.RightOf(current) != null && (!_uBoundActive || Pal.Compare(comparer, _max, SpecSearchTree.RootKey(Pal.Tree<(T, bool)>(current), _min)) > 0)
                        ? Pal.Snoc(q1.Value, Pal.RightOf(current))
                        : q1.Value));
                    Pal.Assert(processQueue.Items == SpecRangeWalk.BfNext<Node, T>(Pal.Heap<Node>(), comparer, _min, _max, _lBoundActive, _uBoundActive, q0.Value));
                }
                return true;
            }

            [Requires("@this.SpecCoherent")]
            [Ensures("(Result != null) == (SpecSearchTree.InRange(@this._underlying.SpecComparer, @this._min, @this._max, @this._lBoundActive, @this._uBoundActive, item) && Pal.KeyIndex(@this._underlying.SpecComparer, @this._underlying.SpecItems, item) >= 0)")]
            [Ensures("@this.SpecCoherent")]
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
                SortedSetCount.RangeRootHeight(_underlying.SpecComparer, _underlying.SpecNodes, _min, _max, _lBoundActive, _uBoundActive);
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
