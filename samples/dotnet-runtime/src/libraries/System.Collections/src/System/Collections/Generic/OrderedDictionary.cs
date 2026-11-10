// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

#if NET
using static System.ArgumentOutOfRangeException;
#else
using static System.Collections.ThrowHelper;
#endif

namespace System.Collections.Generic
{
    /// <summary>
    /// Represents a collection of key/value pairs that are accessible by the key or index.
    /// </summary>
    /// <typeparam name="TKey">The type of the keys in the dictionary.</typeparam>
    /// <typeparam name="TValue">The type of the values in the dictionary.</typeparam>
    /// <remarks>
    /// Operations on the collection have algorithmic complexities that are similar to that of the <see cref="List{T}"/>
    /// class, except with lookups by key similar in complexity to that of <see cref="Dictionary{TKey, TValue}"/>.
    /// </remarks>
    [DebuggerTypeProxy(typeof(OrderedDictionaryDebugView<,>))]
    [DebuggerDisplay("Count = {Count}")]
    [Invariant("0 <= _count && _count <= _entries.Length")]
    [Invariant("(_buckets == null) == (_entries == null)")]
    [Invariant("_buckets.Length == _entries.Length")]
    [Invariant("_entries != null || _count == 0")]
    [Invariant("_entries != null || Pal.Contents(_entries).Length == 0")]
    [Invariant("_entries == null || _entries.Length > 0")]
    [Invariant("_entries == null || _entries.Length <= int.MaxValue")]
    [Invariant("typeof(TKey).IsValueType || _comparer != null")]
    [Invariant("_buckets == null || IntPtr.Size != 8 || _fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)_buckets.Length)")]
    [Invariant("_buckets == null || OrderedDictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _comparer)")]
#if SYSTEM_COLLECTIONS
    public
#else
    internal sealed
#endif
    class OrderedDictionary<TKey, TValue> :
        IDictionary<TKey, TValue>, IReadOnlyDictionary<TKey, TValue>, IDictionary,
        IList<KeyValuePair<TKey, TValue>>, IReadOnlyList<KeyValuePair<TKey, TValue>>, IList
        where TKey : notnull
    {
        /// <summary>The comparer used by the collection. May be null if the default comparer is used.</summary>
        private IEqualityComparer<TKey>? _comparer;
        /// <summary>Indexes into <see cref="_entries"/> for the start of chains; indices are 1-based.</summary>
        private int[]? _buckets;
        /// <summary>Ordered entries in the dictionary.</summary>
        /// <remarks>
        /// Unlike <see cref="Dictionary{TKey, TValue}"/>, removed entries are actually removed rather than left as holes
        /// that can be filled in by subsequent additions. This is done to retain ordering.
        /// </remarks>
        private Entry[]? _entries;
        /// <summary>The number of items in the collection.</summary>
        private int _count;
        /// <summary>Version number used to invalidate an enumerator.</summary>
        [Wrapping] private int _version;
        /// <summary>Multiplier used on 64-bit to enable faster % operations.</summary>
        private ulong _fastModMultiplier;

        [Model]
        private OrderedDictionaryModel<TKey, TValue> Model => new OrderedDictionaryModel<TKey, TValue>
        {
            Count = _count,
            Keys = KeysOf(Pal.Contents(_entries), _count),
            Values = ValuesOf(Pal.Contents(_entries), _count),
            Comparer = _comparer,
            Version = _version,
            Capacity = Pal.Contents(_entries).Length,
        };

        /// <summary>The number of pairs.</summary>
        [Spec]
        public SpecInt SpecCount => Model.Count;

        /// <summary>The keys, in order.</summary>
        [Spec]
        public Seq<TKey> SpecKeys => Model.Keys;

        /// <summary>The values, in order.</summary>
        [Spec]
        public Seq<TValue> SpecValues => Model.Values;

        /// <summary>The comparer the dictionary was built with.</summary>
        [Spec]
        public IEqualityComparer<TKey>? SpecComparer => Model.Comparer;

        [Spec]
        public SpecInt SpecVersion => Model.Version;

        [Spec]
        public SpecInt SpecCapacity => Model.Capacity;

        // The hash table's theory (pal/OrderedDictionary/OrderedDictionaryChain.fst,
        // Pulse.Lib.CSharp.HashChain).
        [Spec]
        [PulseBody("OrderedDictionaryChain.wf $(buckets) $(entries) $(count) $(comparer)")]
        private static bool Wf(Seq<int> buckets, Seq<Entry> entries, SpecInt count, IEqualityComparer<TKey>? comparer)
            => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.keys $(entries) $(count)")]
        private static Seq<TKey> KeysOf(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.values $(entries) $(count)")]
        private static Seq<TValue> ValuesOf(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        /// <summary>Some key of <paramref name="keys"/> is equal to <paramref name="key"/> at <paramref name="comparer"/>.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.mem $(comparer) $(keys) $(key)")]
        public static bool Mem(IEqualityComparer<TKey>? comparer, Seq<TKey> keys, TKey key) => throw new InvalidOperationException();

        /// <summary><paramref name="comparer"/> deems <paramref name="k"/> equal to <paramref name="key"/>.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.key_eq $(comparer) $(k) $(key)")]
        public static bool KeyEq(IEqualityComparer<TKey>? comparer, TKey k, TKey key) => throw new InvalidOperationException();

        /// <summary>The hash code a lookup of <paramref name="key"/> computes.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.hash_of $(comparer) $(key)")]
        public static SpecInt HashOf(IEqualityComparer<TKey>? comparer, TKey key) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.bucket $(buckets) $(entries) $(comparer) $(key)")]
        private static SpecInt Bucket(Seq<int> buckets, Seq<Entry> entries, IEqualityComparer<TKey>? comparer, TKey key)
            => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.search $(buckets) $(entries) $(count) $(comparer) $(key) $(i) $(q)")]
        private static bool Search(Seq<int> buckets, Seq<Entry> entries, SpecInt count, IEqualityComparer<TKey>? comparer,
            TKey key, SpecInt i, SpecInt q) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.hit $(entries) $(comparer) $(key) $(i)")]
        private static bool Hit(Seq<Entry> entries, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i)
            => throw new InvalidOperationException();

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(buckets, entries, count, comparer) && entries.Length > 0")]
        [Ensures("OrderedDictionary<TKey, TValue>.Search(buckets, entries, count, comparer, key, OrderedDictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) - 1, 0)")]
        [Ensures("0 <= OrderedDictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) && OrderedDictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) <= entries.Length")]
        [PulseBody("OrderedDictionaryChain.search_start $(buckets) $(entries) $(count) $(comparer) $(key)")]
        [Conditional("PAL")]
        private static void SearchStart(Seq<int> buckets, Seq<Entry> entries, SpecInt count, IEqualityComparer<TKey>? comparer, TKey key) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Search(buckets, entries, count, comparer, key, i, q)")]
        [Requires("0 <= i && i < entries.Length && !OrderedDictionary<TKey, TValue>.Hit(entries, comparer, key, i)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Search(buckets, entries, count, comparer, key, entries[i].Next, q + 1)")]
        [Ensures("q + 1 <= entries.Length")]
        [PulseBody("OrderedDictionaryChain.search_step $(buckets) $(entries) $(count) $(comparer) $(key) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchStep(Seq<int> buckets, Seq<Entry> entries, SpecInt count, IEqualityComparer<TKey>? comparer,
            TKey key, SpecInt i, SpecInt q) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Search(buckets, entries, count, comparer, key, i, q)")]
        [Requires("OrderedDictionary<TKey, TValue>.Hit(entries, comparer, key, i)")]
        [Ensures("0 <= i && i < count && i < OrderedDictionary<TKey, TValue>.KeysOf(entries, count).Length && OrderedDictionary<TKey, TValue>.KeyEq(comparer, OrderedDictionary<TKey, TValue>.KeysOf(entries, count)[i], key)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Mem(comparer, OrderedDictionary<TKey, TValue>.KeysOf(entries, count), key)")]
        [PulseBody("OrderedDictionaryChain.search_hit $(buckets) $(entries) $(count) $(comparer) $(key) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchHit(Seq<int> buckets, Seq<Entry> entries, SpecInt count, IEqualityComparer<TKey>? comparer,
            TKey key, SpecInt i, SpecInt q) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Search(buckets, entries, count, comparer, key, i, q)")]
        [Requires("!(0 <= i && i < entries.Length)")]
        [Ensures("!OrderedDictionary<TKey, TValue>.Mem(comparer, OrderedDictionary<TKey, TValue>.KeysOf(entries, count), key)")]
        [PulseBody("OrderedDictionaryChain.search_absent $(buckets) $(entries) $(count) $(comparer) $(key) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchAbsent(Seq<int> buckets, Seq<Entry> entries, SpecInt count, IEqualityComparer<TKey>? comparer,
            TKey key, SpecInt i, SpecInt q) { }

        /// <summary><paramref name="entries"/> with the value of entry <paramref name="i"/> replaced.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.set_value $(entries) $(i) $(value)")]
        private static Seq<Entry> SetValue(Seq<Entry> entries, int i, TValue value) => throw new InvalidOperationException();

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(buckets, entries, count, comparer) && 0 <= i && i < count")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wf(buckets, OrderedDictionary<TKey, TValue>.SetValue(entries, i, value), count, comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.KeysOf(OrderedDictionary<TKey, TValue>.SetValue(entries, i, value), count) == OrderedDictionary<TKey, TValue>.KeysOf(entries, count)")]
        [Ensures("count <= entries.Length && i < OrderedDictionary<TKey, TValue>.ValuesOf(entries, count).Length && OrderedDictionary<TKey, TValue>.ValuesOf(OrderedDictionary<TKey, TValue>.SetValue(entries, i, value), count) == Pal.SetAt(OrderedDictionary<TKey, TValue>.ValuesOf(entries, count), i, value)")]
        [PulseBody("OrderedDictionaryChain.wf_set_value $(buckets) $(entries) $(count) $(comparer) (FStar.Int32.v $(i)) $(value)")]
        [Conditional("PAL")]
        private static void WfSetValue(Seq<int> buckets, Seq<Entry> entries, SpecInt count, IEqualityComparer<TKey>? comparer,
            int i, TValue value) { }

        [Lemma]
        [Requires("buckets.Length == entries.Length && Pal.Forall((int b) => Pal.Implies(0 <= b && b < buckets.Length, buckets[b] == 0))")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wf(buckets, entries, 0, comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.KeysOf(entries, 0) == Pal.EmptySeq<TKey>()")]
        [Ensures("OrderedDictionary<TKey, TValue>.ValuesOf(entries, 0) == Pal.EmptySeq<TValue>()")]
        [PulseBody("OrderedDictionaryChain.wf_clear $(buckets) $(entries) $(comparer)")]
        [Conditional("PAL")]
        private static void WfClear(Seq<int> buckets, Seq<Entry> entries, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Ensures("Pal.Implies(OrderedDictionary<TKey, TValue>.Wf(buckets, entries, 0, comparer), OrderedDictionary<TKey, TValue>.Wf(buckets, entries, 0, comparer2))")]
        [PulseBody("OrderedDictionaryChain.wf_rebind $(buckets) $(entries) $(comparer) $(comparer2)")]
        [Conditional("PAL")]
        private static void WfRebind(Seq<int> buckets, Seq<Entry> entries, IEqualityComparer<TKey>? comparer, IEqualityComparer<TKey>? comparer2) { }

        // The table part-way through a shift (`Insert`, `RemoveAt`): entries below `m` but the
        // hole `h` are chained, and `Keysh`/`Valuesh` are their pairs in order.
        [Spec]
        [PulseBody("OrderedDictionaryChain.wfm $(buckets) $(entries) $(m) $(h) $(comparer)")]
        private static bool Wfm(Seq<int> buckets, Seq<Entry> entries, SpecInt m, SpecInt h, IEqualityComparer<TKey>? comparer)
            => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.keysh $(entries) $(m) $(h)")]
        private static Seq<TKey> Keysh(Seq<Entry> entries, SpecInt m, SpecInt h) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.valuesh $(entries) $(m) $(h)")]
        private static Seq<TValue> Valuesh(Seq<Entry> entries, SpecInt m, SpecInt h) => throw new InvalidOperationException();

        /// <summary>Entries <paramref name="h"/> and <paramref name="i"/> are the same.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.copied $(entries) $(h) $(i)")]
        private static bool Copied(Seq<Entry> entries, SpecInt h, SpecInt i) => throw new InvalidOperationException();

        /// <summary>The bucket of entry <paramref name="i"/>.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.bof $(entries) $(i)")]
        private static SpecInt Bof(Seq<Entry> entries, SpecInt i) => throw new InvalidOperationException();

        /// <summary>The walk along entry <paramref name="t"/>'s chain has reached <paramref name="i"/> after <paramref name="q"/> links, before <paramref name="t"/>.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.pred $(buckets) $(entries) $(m) $(h) $(t) $(i) $(q)")]
        private static bool Pred(Seq<int> buckets, Seq<Entry> entries, SpecInt m, SpecInt h, SpecInt t, SpecInt i, SpecInt q)
            => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.move_writes $(bs) $(bs2) $(es) $(es2) $(m) $(h) $(i) $(p) $(q)")]
        private static bool MoveWrites(Seq<int> bs, Seq<int> bs2, Seq<Entry> es, Seq<Entry> es2, SpecInt m, SpecInt h, SpecInt i, SpecInt p, SpecInt q)
            => throw new InvalidOperationException();

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wfm(buckets, entries, m, h, comparer) && 0 <= t && t < m && t != h && t < entries.Length && buckets.Length == entries.Length")]
        [Requires("buckets[OrderedDictionary<TKey, TValue>.Bof(entries, t)] != t + 1")]
        [Ensures("OrderedDictionary<TKey, TValue>.Pred(buckets, entries, m, h, t, buckets[OrderedDictionary<TKey, TValue>.Bof(entries, t)] - 1, 0)")]
        [PulseBody("OrderedDictionaryChain.wfm_pred_start $(buckets) $(entries) $(m) $(h) $(t) $(comparer)")]
        [Conditional("PAL")]
        private static void WfmPredStart(Seq<int> buckets, Seq<Entry> entries, SpecInt m, SpecInt h, SpecInt t, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wfm(buckets, entries, m, h, comparer) && 0 <= b && b < buckets.Length")]
        [Ensures("0 <= buckets[b] && buckets[b] <= entries.Length")]
        [PulseBody("OrderedDictionaryChain.wfm_head $(buckets) $(entries) $(m) $(h) $(comparer) $(b)")]
        [Conditional("PAL")]
        private static void WfmHead(Seq<int> buckets, Seq<Entry> entries, SpecInt m, SpecInt h, IEqualityComparer<TKey>? comparer, SpecInt b) { }

        [Spec]
        [PulseBody("OrderedDictionaryChain.unlink_writes $(bs) $(bs2) $(es) $(es2) $(n) $(x) $(p) $(q)")]
        private static bool UnlinkWrites(Seq<int> bs, Seq<int> bs2, Seq<Entry> es, Seq<Entry> es2, SpecInt n, SpecInt x, SpecInt p, SpecInt q)
            => throw new InvalidOperationException();

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(buckets, entries, n, comparer) && 0 <= x && x < n")]
        [Ensures("x < entries.Length && -1 <= entries[x].Next && entries[x].Next < entries.Length")]
        [PulseBody("OrderedDictionaryChain.wf_next $(buckets) $(entries) $(n) $(x) $(comparer)")]
        [Conditional("PAL")]
        private static void WfNext(Seq<int> buckets, Seq<Entry> entries, SpecInt n, SpecInt x, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(buckets, entries, n, comparer) && 0 <= x && x < n && x < entries.Length && buckets.Length == entries.Length")]
        [Requires("buckets[OrderedDictionary<TKey, TValue>.Bof(entries, x)] != x + 1")]
        [Ensures("OrderedDictionary<TKey, TValue>.Pred(buckets, entries, n, -1, x, buckets[OrderedDictionary<TKey, TValue>.Bof(entries, x)] - 1, 0)")]
        [PulseBody("OrderedDictionaryChain.wf_pred_start $(buckets) $(entries) $(n) $(x) $(comparer)")]
        [Conditional("PAL")]
        private static void WfPredStart(Seq<int> buckets, Seq<Entry> entries, SpecInt n, SpecInt x, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(bs, es, n, comparer) && x < n && OrderedDictionary<TKey, TValue>.UnlinkWrites(bs, bs2, es, es2, n, x, p, q)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wfm(bs2, es2, n, x, comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Keysh(es2, n, x) == OrderedDictionary<TKey, TValue>.Keysh(es, n, x)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Valuesh(es2, n, x) == OrderedDictionary<TKey, TValue>.Valuesh(es, n, x)")]
        [PulseBody("OrderedDictionaryChain.unlink_ok $(bs) $(bs2) $(es) $(es2) $(n) $(x) $(p) $(q) $(comparer)")]
        [Conditional("PAL")]
        private static void UnlinkOk(Seq<int> bs, Seq<int> bs2, Seq<Entry> es, Seq<Entry> es2, SpecInt n, SpecInt x, SpecInt p, SpecInt q,
            IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(buckets, entries, n, comparer) && 0 <= b && b < buckets.Length")]
        [Ensures("0 <= buckets[b] && buckets[b] <= entries.Length")]
        [PulseBody("OrderedDictionaryChain.wf_head $(buckets) $(entries) $(n) $(comparer) $(b)")]
        [Conditional("PAL")]
        private static void WfHead(Seq<int> buckets, Seq<Entry> entries, SpecInt n, IEqualityComparer<TKey>? comparer, SpecInt b) { }

        /// <summary>Below <paramref name="n"/>, <paramref name="entries"/> holds <paramref name="old"/>'s pairs and hash codes.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.same_kvh $(entries) $(old) $(n)")]
        private static bool SameKvh(Seq<Entry> entries, Seq<Entry> old, SpecInt n) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.push_writes $(bs) $(bs2) $(es) $(es2) $(i)")]
        private static bool PushWrites(Seq<int> bs, Seq<int> bs2, Seq<Entry> es, Seq<Entry> es2, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= n && n <= entries.Length && n <= old.Length && Pal.Slice(entries, 0, n) == Pal.Slice(old, 0, n)")]
        [Ensures("OrderedDictionary<TKey, TValue>.SameKvh(entries, old, n)")]
        [PulseBody("OrderedDictionaryChain.same_kvh_copy $(entries) $(old) $(n)")]
        [Conditional("PAL")]
        private static void SameKvhCopy(Seq<Entry> entries, Seq<Entry> old, SpecInt n) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(bs, es, i, comparer) && OrderedDictionary<TKey, TValue>.Wf(ob, old, n, comparer) && 0 <= i && i < n")]
        [Requires("OrderedDictionary<TKey, TValue>.SameKvh(es, old, n) && OrderedDictionary<TKey, TValue>.PushWrites(bs, bs2, es, es2, i)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wf(bs2, es2, i + 1, comparer) && OrderedDictionary<TKey, TValue>.SameKvh(es2, old, n)")]
        [PulseBody("OrderedDictionaryChain.push_step $(bs) $(bs2) $(es) $(es2) $(ob) $(old) $(i) $(n) $(comparer)")]
        [Conditional("PAL")]
        private static void PushStep(Seq<int> bs, Seq<int> bs2, Seq<Entry> es, Seq<Entry> es2, Seq<int> ob, Seq<Entry> old, SpecInt i, SpecInt n,
            IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.SameKvh(entries, old, n)")]
        [Ensures("OrderedDictionary<TKey, TValue>.KeysOf(entries, n) == OrderedDictionary<TKey, TValue>.KeysOf(old, n)")]
        [Ensures("OrderedDictionary<TKey, TValue>.ValuesOf(entries, n) == OrderedDictionary<TKey, TValue>.ValuesOf(old, n)")]
        [PulseBody("OrderedDictionaryChain.resize_pairs $(entries) $(old) $(n)")]
        [Conditional("PAL")]
        private static void ResizePairs(Seq<Entry> entries, Seq<Entry> old, SpecInt n) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Pred(buckets, entries, m, h, t, i, q)")]
        [Ensures("0 <= i && i < entries.Length && q < entries.Length")]
        [PulseBody("OrderedDictionaryChain.pred_range $(buckets) $(entries) $(m) $(h) $(t) $(i) $(q)")]
        [Conditional("PAL")]
        private static void PredRange(Seq<int> buckets, Seq<Entry> entries, SpecInt m, SpecInt h, SpecInt t, SpecInt i, SpecInt q) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Pred(buckets, entries, m, h, t, i, q) && 0 <= i && i < entries.Length && entries[i].Next != t")]
        [Ensures("OrderedDictionary<TKey, TValue>.Pred(buckets, entries, m, h, t, entries[i].Next, q + 1) && q + 1 < entries.Length")]
        [PulseBody("OrderedDictionaryChain.pred_step $(buckets) $(entries) $(m) $(h) $(t) $(i) $(q)")]
        [Conditional("PAL")]
        private static void PredStep(Seq<int> buckets, Seq<Entry> entries, SpecInt m, SpecInt h, SpecInt t, SpecInt i, SpecInt q) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wfm(bs, es, m, h, comparer) && 0 <= i && i < m && (i == h + 1 || i == h - 1)")]
        [Requires("OrderedDictionary<TKey, TValue>.Copied(es, h, i) && OrderedDictionary<TKey, TValue>.MoveWrites(bs, bs2, es, es2, m, h, i, p, q)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wfm(bs2, es2, m, i, comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Keysh(es2, m, i) == OrderedDictionary<TKey, TValue>.Keysh(es, m, h)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Valuesh(es2, m, i) == OrderedDictionary<TKey, TValue>.Valuesh(es, m, h)")]
        [PulseBody("OrderedDictionaryChain.move_ok $(bs) $(bs2) $(es) $(es2) $(m) $(h) $(i) $(p) $(q) $(comparer)")]
        [Conditional("PAL")]
        private static void MoveOk(Seq<int> bs, Seq<int> bs2, Seq<Entry> es, Seq<Entry> es2, SpecInt m, SpecInt h, SpecInt i, SpecInt p, SpecInt q,
            IEqualityComparer<TKey>? comparer) { }

        /// <summary><paramref name="c"/> if it is not null, otherwise <see cref="EqualityComparer{TKey}.Default"/>.</summary>
        // Inserting and removing pairs (`TryInsert`, `RemoveAt`, `SetAt`).
        [Spec]
        [PulseBody("OrderedDictionaryChain.ins $(s) $(i) $(x)")]
        public static Seq<TKey> InsK(Seq<TKey> s, SpecInt i, TKey x) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.ins $(s) $(i) $(x)")]
        public static Seq<TValue> InsV(Seq<TValue> s, SpecInt i, TValue x) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.del $(s) $(i)")]
        public static Seq<TKey> DelK(Seq<TKey> s, SpecInt i) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.del $(s) $(i)")]
        public static Seq<TValue> DelV(Seq<TValue> s, SpecInt i) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("OrderedDictionaryChain.same_off $(es) $(es2) $(h)")]
        private static bool SameOff(Seq<Entry> es, Seq<Entry> es2, SpecInt h) => throw new InvalidOperationException();

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wfm(bs, es, m, h, comparer) && OrderedDictionary<TKey, TValue>.SameOff(es, es2, h)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wfm(bs, es2, m, h, comparer) && es2.Length == es.Length")]
        [Ensures("OrderedDictionary<TKey, TValue>.Keysh(es2, m, h) == OrderedDictionary<TKey, TValue>.Keysh(es, m, h) && OrderedDictionary<TKey, TValue>.Valuesh(es2, m, h) == OrderedDictionary<TKey, TValue>.Valuesh(es, m, h)")]
        [PulseBody("OrderedDictionaryChain.hole_eq $(bs) $(es) $(es2) $(m) $(h) $(comparer)")]
        [Conditional("PAL")]
        private static void HoleEq(Seq<int> bs, Seq<Entry> es, Seq<Entry> es2, SpecInt m, SpecInt h, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wfm(bs, es, m, h, comparer) && OrderedDictionary<TKey, TValue>.PushWrites(bs, bs2, es, es2, h)")]
        [Requires("h < es.Length && es[h].HashCode == OrderedDictionary<TKey, TValue>.HashOf(comparer, es[h].Key)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wf(bs2, es2, m, comparer) && es2.Length == es.Length && bs2.Length == bs.Length")]
        [Ensures("OrderedDictionary<TKey, TValue>.KeysOf(es2, m) == OrderedDictionary<TKey, TValue>.InsK(OrderedDictionary<TKey, TValue>.Keysh(es, m, h), h, es[h].Key)")]
        [Ensures("OrderedDictionary<TKey, TValue>.ValuesOf(es2, m) == OrderedDictionary<TKey, TValue>.InsV(OrderedDictionary<TKey, TValue>.Valuesh(es, m, h), h, es[h].Value)")]
        [PulseBody("OrderedDictionaryChain.fill_step $(bs) $(bs2) $(es) $(es2) $(m) $(h) $(comparer)")]
        [Conditional("PAL")]
        private static void FillStep(Seq<int> bs, Seq<int> bs2, Seq<Entry> es, Seq<Entry> es2, SpecInt m, SpecInt h, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(bs, es, n, comparer) && 0 <= n && n < es.Length && bs.Length == es.Length")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wfm(bs, es, n + 1, n, comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Keysh(es, n + 1, n) == OrderedDictionary<TKey, TValue>.KeysOf(es, n) && OrderedDictionary<TKey, TValue>.Valuesh(es, n + 1, n) == OrderedDictionary<TKey, TValue>.ValuesOf(es, n)")]
        [PulseBody("OrderedDictionaryChain.open_ok' $(bs) $(es) $(n) $(comparer)")]
        [Conditional("PAL")]
        private static void OpenOk(Seq<int> bs, Seq<Entry> es, SpecInt n, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("OrderedDictionary<TKey, TValue>.Wfm(bs, es, n, n - 1, comparer) && OrderedDictionary<TKey, TValue>.SameOff(es, es2, n - 1)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wf(bs, es2, n - 1, comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.KeysOf(es2, n - 1) == OrderedDictionary<TKey, TValue>.Keysh(es, n, n - 1) && OrderedDictionary<TKey, TValue>.ValuesOf(es2, n - 1) == OrderedDictionary<TKey, TValue>.Valuesh(es, n, n - 1)")]
        [PulseBody("OrderedDictionaryChain.close_ok' $(bs) $(es) $(es2) $(n) $(comparer)")]
        [Conditional("PAL")]
        private static void CloseOk(Seq<int> bs, Seq<Entry> es, Seq<Entry> es2, SpecInt n, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("0 <= x && x < n && n <= es.Length")]
        [Ensures("OrderedDictionary<TKey, TValue>.Keysh(es, n, x) == OrderedDictionary<TKey, TValue>.DelK(OrderedDictionary<TKey, TValue>.KeysOf(es, n), x) && OrderedDictionary<TKey, TValue>.Valuesh(es, n, x) == OrderedDictionary<TKey, TValue>.DelV(OrderedDictionary<TKey, TValue>.ValuesOf(es, n), x)")]
        [Ensures("OrderedDictionary<TKey, TValue>.KeysOf(es, n).Length == n && OrderedDictionary<TKey, TValue>.ValuesOf(es, n).Length == n")]
        [PulseBody("OrderedDictionaryChain.keysh_del' $(es) $(n) $(x)")]
        [Conditional("PAL")]
        private static void KeyshDel(Seq<Entry> es, SpecInt n, SpecInt x) { }

        [Lemma]
        [Requires("0 <= i && i < s.Length")]
        [Ensures("OrderedDictionary<TKey, TValue>.InsK(OrderedDictionary<TKey, TValue>.DelK(s, i), i, x) == Pal.SetAt(s, i, x)")]
        [PulseBody("OrderedDictionaryChain.ins_del $(s) (FStar.Int32.v $(i)) $(x)")]
        [Conditional("PAL")]
        private static void InsDelK(Seq<TKey> s, int i, TKey x) { }

        [Lemma]
        [Requires("0 <= i && i < s.Length")]
        [Ensures("OrderedDictionary<TKey, TValue>.InsV(OrderedDictionary<TKey, TValue>.DelV(s, i), i, x) == Pal.SetAt(s, i, x)")]
        [PulseBody("OrderedDictionaryChain.ins_del $(s) (FStar.Int32.v $(i)) $(x)")]
        [Conditional("PAL")]
        private static void InsDelV(Seq<TValue> s, int i, TValue x) { }

        [Spec]
        [PulseBody("(match $(c) with | Some x -> x | None -> Pulse.Lib.CSharp.Equality.default_comparer $(TKey))")]
        public static IEqualityComparer<TKey> OrDefault(IEqualityComparer<TKey>? c) => throw new InvalidOperationException();

        /// <summary>Some value of <paramref name="values"/> below <paramref name="i"/> is equal to <paramref name="value"/> at the default comparer.</summary>
        [Spec]
        [PulseBody("OrderedDictionaryChain.has_value $(values) $(value) $(i)")]
        public static bool HasValue(Seq<TValue> values, TValue value, SpecInt i) => throw new InvalidOperationException();

        /// <summary>
        /// Initializes a new instance of the <see cref="OrderedDictionary{TKey, TValue}"/> class that is empty,
        /// has the default initial capacity, and uses the default equality comparer for the key type.
        /// </summary>
        [Ensures("@this.SpecCount == 0")]
        [Ensures("OrderedDictionary<TKey, TValue>.OrDefault(@this.SpecComparer) == EqualityComparer<TKey>.Default")]
        public OrderedDictionary() : this(0, null)
        {
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="OrderedDictionary{TKey, TValue}"/> class that is empty,
        /// has the specified initial capacity, and uses the default equality comparer for the key type.
        /// </summary>
        /// <param name="capacity">The initial number of elements that the <see cref="OrderedDictionary{TKey, TValue}"/> can contain.</param>
        /// <exception cref="ArgumentOutOfRangeException">capacity is less than 0.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == 0 && @this.SpecCapacity >= capacity")]
        [Ensures("OrderedDictionary<TKey, TValue>.OrDefault(@this.SpecComparer) == EqualityComparer<TKey>.Default")]
        public OrderedDictionary(int capacity) : this(capacity, null)
        {
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="OrderedDictionary{TKey, TValue}"/> class that is empty,
        /// has the default initial capacity, and uses the specified <see cref="IEqualityComparer{TKey}"/>.
        /// </summary>
        /// <param name="comparer">
        /// The <see cref="IEqualityComparer{TKey}"/> implementation to use when comparing keys,
        /// or null to use the default <see cref="EqualityComparer{TKey}"/> for the type of the key.
        /// </param>
        [Ensures("@this.SpecCount == 0")]
        [Ensures("OrderedDictionary<TKey, TValue>.OrDefault(@this.SpecComparer) == OrderedDictionary<TKey, TValue>.OrDefault(comparer)")]
        public OrderedDictionary(IEqualityComparer<TKey>? comparer) : this(0, comparer)
        {
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="OrderedDictionary{TKey, TValue}"/> class that is empty,
        /// has the specified initial capacity, and uses the specified <see cref="IEqualityComparer{TKey}"/>.
        /// </summary>
        /// <param name="capacity">The initial number of elements that the <see cref="OrderedDictionary{TKey, TValue}"/> can contain.</param>
        /// <param name="comparer">
        /// The <see cref="IEqualityComparer{TKey}"/> implementation to use when comparing keys,
        /// or null to use the default <see cref="EqualityComparer{TKey}"/> for the type of the key.
        /// </param>
        /// <exception cref="ArgumentOutOfRangeException"><paramref name="capacity"/> is less than 0.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == 0 && @this.SpecCapacity >= capacity")]
        [Ensures("OrderedDictionary<TKey, TValue>.OrDefault(@this.SpecComparer) == OrderedDictionary<TKey, TValue>.OrDefault(comparer)")]
        public OrderedDictionary(int capacity, IEqualityComparer<TKey>? comparer)
        {
            ThrowIfNegative(capacity);

            if (capacity > 0)
            {
                EnsureBucketsAndEntriesInitialized(capacity);
            }

            // Initialize the comparer:
            // - Strings: Special-case EqualityComparer<string>.Default, StringComparer.Ordinal, and
            //   StringComparer.OrdinalIgnoreCase. We start with a non-randomized comparer for improved throughput,
            //   falling back to a randomized comparer if the hash buckets become sufficiently unbalanced to cause
            //   more collisions than a preset threshold.
            // - Other reference types: we always want to store a comparer instance, either the one provided,
            //   or if one wasn't provided, the default (accessing EqualityComparer<TKey>.Default
            //   with shared generics on every dictionary access can add measurable overhead).
            // - Value types: if no comparer is provided, or if the default is provided, we'd prefer to use
            //   EqualityComparer<TKey>.Default.Equals on every use, enabling the JIT to
            //   devirtualize and possibly inline the operation.
            if (!typeof(TKey).IsValueType)
            {
                _comparer = comparer ?? EqualityComparer<TKey>.Default;

#if SYSTEM_COLLECTIONS
                if (typeof(TKey) == typeof(string) &&
                    NonRandomizedStringEqualityComparer.GetStringComparer(_comparer) is IEqualityComparer<string> stringComparer)
                {
                    _comparer = (IEqualityComparer<TKey>)stringComparer;
                }
#endif
            }
            else if (comparer is not null && // first check for null to avoid forcing default comparer instantiation unnecessarily
                     comparer != EqualityComparer<TKey>.Default)
            {
                _comparer = comparer;
            }

            WfRebind(Pal.Contents(_buckets), Pal.Contents(_entries), null, _comparer);
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="OrderedDictionary{TKey, TValue}"/> class that contains elements copied from
        /// the specified <see cref="IDictionary{TKey, TValue}"/> and uses the default equality comparer for the key type.
        /// </summary>
        /// <param name="dictionary">
        /// The <see cref="IDictionary{TKey, TValue}"/> whose elements are copied to the new <see cref="OrderedDictionary{TKey, TValue}"/>.
        /// The initial order of the elements in the new collection is the order the elements are enumerated from the supplied dictionary.
        /// </param>
        /// <exception cref="ArgumentNullException"><paramref name="dictionary"/> is <see langword="null"/>.</exception>
        public OrderedDictionary(IDictionary<TKey, TValue> dictionary) : this(dictionary, null)
        {
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="OrderedDictionary{TKey, TValue}"/> class that contains elements copied from
        /// the specified <see cref="IDictionary{TKey, TValue}"/> and uses the specified <see cref="IEqualityComparer{TKey}"/>.
        /// </summary>
        /// <param name="dictionary">
        /// The <see cref="IDictionary{TKey, TValue}"/> whose elements are copied to the new <see cref="OrderedDictionary{TKey, TValue}"/>.
        /// The initial order of the elements in the new collection is the order the elements are enumerated from the supplied dictionary.
        /// </param>
        /// <param name="comparer">
        /// The <see cref="IEqualityComparer{TKey}"/> implementation to use when comparing keys,
        /// or null to use the default <see cref="EqualityComparer{TKey}"/> for the type of the key.
        /// </param>
        /// <exception cref="ArgumentNullException"><paramref name="dictionary"/> is <see langword="null"/>.</exception>
        public OrderedDictionary(IDictionary<TKey, TValue> dictionary, IEqualityComparer<TKey>? comparer) :
            this(dictionary?.Count ?? 0, comparer)
        {
            ArgumentNullException.ThrowIfNull(dictionary);

            AddRange(dictionary);
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="OrderedDictionary{TKey, TValue}"/> class that contains elements copied
        /// from the specified <see cref="IEnumerable{T}"/> and uses the default equality comparer for the key type.
        /// </summary>
        /// <param name="collection">
        /// The <see cref="IEnumerable{T}"/> whose elements are copied to the new <see cref="OrderedDictionary{TKey, TValue}"/>.
        /// The initial order of the elements in the new collection is the order the elements are enumerated from the supplied collection.
        /// </param>
        /// <exception cref="ArgumentNullException"><paramref name="collection"/> is <see langword="null"/>.</exception>
        public OrderedDictionary(IEnumerable<KeyValuePair<TKey, TValue>> collection) : this(collection, null)
        {
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="OrderedDictionary{TKey, TValue}"/> class that contains elements copied
        /// from the specified <see cref="IEnumerable{T}"/> and uses the specified <see cref="IEqualityComparer{TKey}"/>.
        /// </summary>
        /// <param name="collection">
        /// The <see cref="IEnumerable{T}"/> whose elements are copied to the new <see cref="OrderedDictionary{TKey, TValue}"/>.
        /// The initial order of the elements in the new collection is the order the elements are enumerated from the supplied collection.
        /// </param>
        /// <param name="comparer">
        /// The <see cref="IEqualityComparer{TKey}"/> implementation to use when comparing keys,
        /// or null to use the default <see cref="EqualityComparer{TKey}"/> for the type of the key.
        /// </param>
        /// <exception cref="ArgumentNullException"><paramref name="collection"/> is <see langword="null"/>.</exception>
        public OrderedDictionary(IEnumerable<KeyValuePair<TKey, TValue>> collection, IEqualityComparer<TKey>? comparer) :
            this((collection as ICollection<KeyValuePair<TKey, TValue>>)?.Count ?? 0, comparer)
        {
            ArgumentNullException.ThrowIfNull(collection);

            AddRange(collection);
        }

        /// <summary>Initializes the <see cref="_buckets"/>/<see cref="_entries"/>.</summary>
        /// <param name="capacity"></param>
        [MemberNotNull(nameof(_buckets))]
        [MemberNotNull(nameof(_entries))]
        [Open]
        [Requires("capacity >= 0 && @this._buckets == null && @this._entries == null && @this._count == 0")]
        [Requires("Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length && Pal.Contents(@this._entries).Length == 0")]
        [Ensures("@this._buckets != null && @this._entries != null")]
        [Ensures("Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length && Pal.Contents(@this._entries).Length >= capacity && Pal.Contents(@this._entries).Length > 0 && Pal.Contents(@this._entries).Length <= int.MaxValue")]
        [Ensures("Pal.Implies(capacity <= System.Collections.HashHelpers.MaxPrimeArrayLength, Pal.Contents(@this._entries).Length <= System.Collections.HashHelpers.MaxPrimeArrayLength)")]
        [Ensures("IntPtr.Size != 8 || @this._fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)Pal.Contents(@this._buckets).Length)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wf(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count, @this._comparer)")]
        private void EnsureBucketsAndEntriesInitialized(int capacity)
        {
            Resize(HashHelpers.GetPrime(capacity));
        }

        /// <summary>Gets the total number of key/value pairs the internal data structure can hold without resizing.</summary>
        [Ensures("Result == @this.SpecCapacity")]
        public int Capacity => _entries?.Length ?? 0;

        /// <summary>Gets the <see cref="IEqualityComparer{TKey}"/> that is used to determine equality of keys for the dictionary.</summary>
        [Ensures("Result == OrderedDictionary<TKey, TValue>.OrDefault(@this.SpecComparer)")]
        public IEqualityComparer<TKey> Comparer
        {
            get
            {
                IEqualityComparer<TKey>? comparer = _comparer;

#if SYSTEM_COLLECTIONS
                // If the key is a string, we may have substituted a non-randomized comparer during construction.
                // If we did, fish out and return the actual comparer that had been provided.
                if (typeof(TKey) == typeof(string) &&
                    (comparer as NonRandomizedStringEqualityComparer)?.GetUnderlyingEqualityComparer() is IEqualityComparer<TKey> ec)
                {
                    return ec;
                }
#endif

                // Otherwise, return whatever comparer we have, or the default if none was provided.
                return comparer ?? EqualityComparer<TKey>.Default;
            }
        }

        /// <summary>Gets the number of key/value pairs contained in the <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        [Ensures("Result == @this.SpecCount && 0 <= Result")]
        public int Count => _count;

        /// <inheritdoc/>
        [Ensures("!Result")]
        bool ICollection<KeyValuePair<TKey, TValue>>.IsReadOnly => false;

        /// <inheritdoc/>
        [Ensures("!Result")]
        bool IDictionary.IsReadOnly => false;

        /// <inheritdoc/>
        [Ensures("!Result")]
        bool IList.IsReadOnly => false;

        /// <inheritdoc/>
        [Ensures("!Result")]
        bool IDictionary.IsFixedSize => false;

        /// <inheritdoc/>
        [Ensures("!Result")]
        bool IList.IsFixedSize => false;

        /// <summary>Gets a collection containing the keys in the <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        [Ensures("ReferenceEquals(Result._dictionary, @this)")]
        public KeyCollection Keys => field ??= new(this);

        /// <inheritdoc/>
        [Ensures("Pal.Exists((OrderedDictionary<TKey, TValue>.KeyCollection c) => Pal.Boxes(Result, c) && ReferenceEquals(c._dictionary, @this))")]
        IEnumerable<TKey> IReadOnlyDictionary<TKey, TValue>.Keys => Keys;

        /// <inheritdoc/>
        [Ensures("Pal.Exists((OrderedDictionary<TKey, TValue>.KeyCollection c) => Pal.Boxes(Result, c) && ReferenceEquals(c._dictionary, @this))")]
        ICollection<TKey> IDictionary<TKey, TValue>.Keys => Keys;

        /// <inheritdoc/>
        [Ensures("Pal.Exists((OrderedDictionary<TKey, TValue>.KeyCollection c) => Pal.Boxes(Result, c) && ReferenceEquals(c._dictionary, @this))")]
        ICollection IDictionary.Keys => Keys;

        /// <summary>Gets a collection containing the values in the <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        [Ensures("ReferenceEquals(Result._dictionary, @this)")]
        public ValueCollection Values => field ??= new(this);

        /// <inheritdoc/>
        [Ensures("Pal.Exists((OrderedDictionary<TKey, TValue>.ValueCollection c) => Pal.Boxes(Result, c) && ReferenceEquals(c._dictionary, @this))")]
        IEnumerable<TValue> IReadOnlyDictionary<TKey, TValue>.Values => Values;

        /// <inheritdoc/>
        [Ensures("Pal.Exists((OrderedDictionary<TKey, TValue>.ValueCollection c) => Pal.Boxes(Result, c) && ReferenceEquals(c._dictionary, @this))")]
        ICollection<TValue> IDictionary<TKey, TValue>.Values => Values;

        /// <inheritdoc/>
        [Ensures("Pal.Exists((OrderedDictionary<TKey, TValue>.ValueCollection c) => Pal.Boxes(Result, c) && ReferenceEquals(c._dictionary, @this))")]
        ICollection IDictionary.Values => Values;

        /// <inheritdoc/>
        [Ensures("!Result")]
        bool ICollection.IsSynchronized => false;

        /// <inheritdoc/>
        object ICollection.SyncRoot => this;

        /// <inheritdoc/>
        object? IList.this[int index]
        {
            [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
            [Ensures("0 <= index && index < @this.SpecCount && index < @this.SpecKeys.Length && index < @this.SpecValues.Length")]
            [Ensures("Pal.Exists((KeyValuePair<TKey, TValue> p) => Pal.Boxes(Result, p) && Pal.Same(p.Key, @this.SpecKeys[index]) && Pal.Same(p.Value, @this.SpecValues[index]))")]
            get => GetAt(index);
            [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
            [Throws(typeof(ArgumentNullException), "Pal.IsNull(value) || (Pal.IsA<KeyValuePair<TKey, TValue>>(value) && Pal.IsNull(Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key))")]
            [Throws(typeof(ArgumentException), "!Pal.IsA<KeyValuePair<TKey, TValue>>(value) || OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key)")]
            [Ensures("Pal.IsA<KeyValuePair<TKey, TValue>>(value) && 0 <= index && index < Pal.Old(@this.SpecCount) && index < Pal.Old(@this.SpecKeys).Length && index < Pal.Old(@this.SpecValues).Length")]
            [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecComparer == Pal.Old(@this.SpecComparer) && @this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
            [Ensures("@this.SpecValues == Pal.SetAt(Pal.Old(@this.SpecValues), index, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value)")]
            [Ensures("Pal.Implies(0 <= index && index < Pal.Old(@this.SpecKeys).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key, Pal.Old(@this.SpecKeys)[index]), @this.SpecKeys == Pal.Old(@this.SpecKeys))")]
            [Ensures("Pal.Implies(0 <= index && index < Pal.Old(@this.SpecKeys).Length && !OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key, Pal.Old(@this.SpecKeys)[index]), @this.SpecKeys == Pal.SetAt(Pal.Old(@this.SpecKeys), index, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key))")]
            set
            {
                ArgumentNullException.ThrowIfNull(value);

                if (value is not KeyValuePair<TKey, TValue> tpair)
                {
                    throw new ArgumentException(SR.Format(SR.Arg_WrongType, value, typeof(KeyValuePair<TKey, TValue>)), nameof(value));
                }

                SetAt(index, tpair.Key, tpair.Value);
            }
        }

        /// <inheritdoc/>
        object? IDictionary.this[object key]
        {
            [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
            [Ensures("Pal.Implies(!(Pal.IsA<TKey>(key) && OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<TKey>(key))), Pal.IsNull(Result))")]
            [Ensures("Pal.Implies(Pal.IsA<TKey>(key) && OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<TKey>(key)), Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], Pal.Unbox<TKey>(key)) && Pal.Boxes(Result, @this.SpecValues[i])))")]
            get
            {
                ArgumentNullException.ThrowIfNull(key);

                if (key is TKey tkey && TryGetValue(tkey, out TValue? value))
                {
                    return value;
                }

                return null;
            }
            [Throws(typeof(ArgumentNullException), "Pal.IsNull(key) || (Pal.IsNull(value) && !Pal.IsNull(default(TValue)))")]
            [Throws(typeof(ArgumentException), "!Pal.IsA<TKey>(key) || (!Pal.IsNull(value) && !Pal.IsA<TValue>(value)) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
            [Ensures("Pal.IsA<TKey>(key) && (Pal.IsNull(value) || Pal.IsA<TValue>(value)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
            [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<TKey>(key))), @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys))")]
            [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<TKey>(key))), Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < Pal.Old(@this.SpecValues).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], Pal.Unbox<TKey>(key)) && @this.SpecValues == Pal.SetAt(Pal.Old(@this.SpecValues), i, (Pal.IsA<TValue>(value) ? Pal.Unbox<TValue>(value) : default(TValue)))))")]
            [Ensures("Pal.Implies(!Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<TKey>(key))), @this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), Pal.Old(@this.SpecCount), Pal.Unbox<TKey>(key)) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), Pal.Old(@this.SpecCount), (Pal.IsA<TValue>(value) ? Pal.Unbox<TValue>(value) : default(TValue))))")]
            set
            {
                ArgumentNullException.ThrowIfNull(key);
                if (default(TValue) is not null)
                {
                    ArgumentNullException.ThrowIfNull(value);
                }

                if (key is not TKey tkey)
                {
                    throw new ArgumentException(SR.Format(SR.Arg_WrongType, key, typeof(TKey)), nameof(key));
                }

                TValue tvalue = default!;
                if (value is not null)
                {
                    if (value is not TValue temp)
                    {
                        throw new ArgumentException(SR.Format(SR.Arg_WrongType, value, typeof(TValue)), nameof(value));
                    }

                    tvalue = temp;
                }

                this[tkey] = tvalue;
            }
        }

        /// <inheritdoc/>
        KeyValuePair<TKey, TValue> IList<KeyValuePair<TKey, TValue>>.this[int index]
        {
            [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
            [Ensures("0 <= index && index < @this.SpecCount")]
            [Ensures("index < @this.SpecKeys.Length && index < @this.SpecValues.Length && Pal.Same(Result.Key, @this.SpecKeys[index]) && Pal.Same(Result.Value, @this.SpecValues[index])")]
            get => GetAt(index);
            set => SetAt(index, value.Key, value.Value);
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
        [Ensures("0 <= index && index < @this.SpecCount")]
        [Ensures("index < @this.SpecKeys.Length && index < @this.SpecValues.Length && Pal.Same(Result.Key, @this.SpecKeys[index]) && Pal.Same(Result.Value, @this.SpecValues[index])")]
        KeyValuePair<TKey, TValue> IReadOnlyList<KeyValuePair<TKey, TValue>>.this[int index] => GetAt(index);

        /// <summary>Gets or sets the value associated with the specified key.</summary>
        /// <param name="key">The key of the value to get or set.</param>
        /// <returns>The value associated with the specified key. If the specified key is not found, a get operation throws a <see cref="KeyNotFoundException"/>, and a set operation creates a new element with the specified key.</returns>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        /// <exception cref="KeyNotFoundException">The property is retrieved and <paramref name="key"/> does not exist in the collection.</exception>
        /// <remarks>Setting the value of an existing key does not impact its order in the collection.</remarks>
        public TValue this[TKey key]
        {
            [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
            [Throws(typeof(KeyNotFoundException), "!OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
            [Ensures("Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], key) && Pal.Same(Result, @this.SpecValues[i]))")]
            get
            {
                if (!TryGetValue(key, out TValue? value))
                {
                    ThrowHelper.ThrowKeyNotFound(key);
                }

                return value;
            }
            [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
            [Throws(typeof(ArgumentException), "@this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
            [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
            [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)), @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys))")]
            [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)), Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < Pal.Old(@this.SpecValues).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], key) && @this.SpecValues == Pal.SetAt(Pal.Old(@this.SpecValues), i, value)))")]
            [Ensures("Pal.Implies(!Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)), @this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), Pal.Old(@this.SpecCount), key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), Pal.Old(@this.SpecCount), value))")]
            set
            {
                ArgumentNullException.ThrowIfNull(key);

                bool modified = TryInsert(index: -1, key, value, InsertionBehavior.OverwriteExisting, out _);
                Debug.Assert(modified);
            }
        }

        /// <summary>Insert the key/value pair at the specified index.</summary>
        /// <param name="index">The index at which to insert the pair, or -1 to append.</param>
        /// <param name="key">The key to insert.</param>
        /// <param name="value">The value to insert.</param>
        /// <param name="behavior">
        /// The behavior controlling insertion behavior with respect to key duplication:
        /// - IgnoreInsertion: Immediately ends the operation, returning false, if the key already exists, e.g. TryAdd(key, value)
        /// - OverwriteExisting: If the key already exists, overwrites its value with the specified value, e.g. this[key] = value
        /// - ThrowOnExisting: If the key already exists, throws an exception, e.g. Add(key, value)
        /// </param>
        /// <param name="keyIndex">The index of the added or existing key. This is always a valid index into the dictionary.</param>
        /// <returns>true if the collection was updated; otherwise, false.</returns>
        [Requires("key != null && (index < 0 || index <= @this.SpecCount)")]
        [Requires("behavior == InsertionBehavior.IgnoreInsertion || behavior == InsertionBehavior.OverwriteExisting || behavior == InsertionBehavior.ThrowOnExisting")]
        [Requires("index < 0 || behavior == InsertionBehavior.ThrowOnExisting")]
        [Throws(typeof(ArgumentException), "(behavior == InsertionBehavior.ThrowOnExisting && OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)), 0 <= keyIndex && keyIndex < @this.SpecCount && keyIndex < @this.SpecKeys.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[keyIndex], key))")]
        [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)), @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && Result == (behavior == InsertionBehavior.OverwriteExisting))")]
        [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) && behavior == InsertionBehavior.OverwriteExisting, 0 <= keyIndex && keyIndex < Pal.Old(@this.SpecValues).Length && @this.SpecValues == Pal.SetAt(Pal.Old(@this.SpecValues), keyIndex, value))")]
        [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) && behavior != InsertionBehavior.OverwriteExisting, @this.SpecValues == Pal.Old(@this.SpecValues))")]
        [Ensures("Pal.Implies(!Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)), Result && keyIndex == (index < 0 ? Pal.Old(@this.SpecCount) : index) && @this.SpecCount == Pal.Old(@this.SpecCount) + 1)")]
        [Ensures("Pal.Implies(!Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)), @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), keyIndex, key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), keyIndex, value))")]
        [Ensures("Pal.Implies(Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)), behavior != InsertionBehavior.ThrowOnExisting)")]
        private bool TryInsert(int index, TKey key, TValue value, InsertionBehavior behavior, out int keyIndex)
        {
            // Search for the key in the dictionary.
            uint hashCode = 0, collisionCount = 0;
            int i = IndexOf(key, ref hashCode, ref collisionCount);

            // Handle the case where the key already exists, based on the requested behavior.
            if (i >= 0)
            {
                keyIndex = i;
                Debug.Assert(0 <= keyIndex && keyIndex < _count);

                Debug.Assert(_entries is not null);

                switch (behavior)
                {
                    case InsertionBehavior.OverwriteExisting:
                        Debug.Assert(index < 0, "Expected index to be unspecied when overwriting an existing key.");
                        WfSetValue(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _comparer, i, value);
                        _entries[i].Value = value;
                        return true;

                    case InsertionBehavior.ThrowOnExisting:
                        ThrowHelper.ThrowDuplicateKey(key);
                        break;

                    default:
                        Debug.Assert(behavior is InsertionBehavior.IgnoreInsertion, $"Unknown behavior: {behavior}");
                        Debug.Assert(index < 0, "Expected index to be unspecied when ignoring a duplicate key.");
                        return false;
                }
            }

            // The key doesn't exist. If a non-negative index was provided, that is the desired index at which to insert,
            // which should have already been validated by the caller. If negative, we're appending.
            if (index < 0)
            {
                index = _count;
            }
            Debug.Assert(index <= _count);

            // Ensure the collection has been initialized.
            if (_buckets is null)
            {
                EnsureBucketsAndEntriesInitialized(0);
            }

            // As we just initialized the collection, _entries must be non-null.
            Entry[]? entries = _entries;
            Debug.Assert(entries is not null);

            // Grow capacity if necessary to accommodate the extra entry.
            if (entries.Length == _count)
            {
                Resize(HashHelpers.ExpandPrime(entries.Length));
                entries = _entries;
            }

            int count = _count;
            Ghost<Seq<TKey>> keys0 = KeysOf(Pal.Contents(_entries), count);
            Ghost<Seq<TValue>> values0 = ValuesOf(Pal.Contents(_entries), count);
            Ghost<int> capacity0 = Pal.Contents(_entries).Length;
            OpenOk(Pal.Contents(_buckets), Pal.Contents(_entries), count, _comparer);

            // The _entries array is ordered, so we need to insert the new entry at the specified index. That means
            // not only shifting up all elements at that index and higher, but also updating the buckets and chains
            // to record the newly updated indices.
            for (i = _count - 1; i >= index; --i)
            {
                Pal.Decreases(i + 1);
                Pal.Invariant(index - 1 <= i && i < count && _count == count && 0 <= index);
                Pal.Invariant(entries == _entries && _buckets != null && _entries != null);
                Pal.Invariant(Pal.Contents(_buckets).Length == Pal.Contents(_entries).Length && count < Pal.Contents(_entries).Length);
                Pal.Invariant(Pal.Contents(_entries).Length == capacity0.Value && capacity0.Value <= int.MaxValue);
                Pal.Invariant(IntPtr.Size != 8 || _fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)Pal.Contents(_buckets).Length));
                Pal.Invariant(Wfm(Pal.Contents(_buckets), Pal.Contents(_entries), count + 1, i + 1, _comparer));
                Pal.Invariant(Keysh(Pal.Contents(_entries), count + 1, i + 1) == keys0.Value);
                Pal.Invariant(Valuesh(Pal.Contents(_entries), count + 1, i + 1) == values0.Value);
                Ghost<Seq<Entry>> e1 = Pal.Contents(_entries);
                entries[i + 1] = entries[i];
                HoleEq(Pal.Contents(_buckets), e1.Value, Pal.Contents(_entries), count + 1, i + 1, _comparer);
                UpdateBucketIndex(i, shiftAmount: 1);
            }

            // Store the new key/value pair.
            Ghost<Seq<Entry>> e2 = Pal.Contents(_entries);
            Pal.Assert(Keysh(e2.Value, count + 1, index) == keys0.Value && Valuesh(e2.Value, count + 1, index) == values0.Value);
            ref Entry entry = ref entries[index];
            entry.HashCode = hashCode;
            entry.Key = key;
            entry.Value = value;
            HoleEq(Pal.Contents(_buckets), e2.Value, Pal.Contents(_entries), count + 1, index, _comparer);
            Pal.Assert(Keysh(Pal.Contents(_entries), count + 1, index) == keys0.Value && Valuesh(Pal.Contents(_entries), count + 1, index) == values0.Value);
            Ghost<Seq<int>> b3 = Pal.Contents(_buckets);
            Ghost<Seq<Entry>> e3 = Pal.Contents(_entries);
            WfmHead(Pal.Contents(_buckets), Pal.Contents(_entries), count + 1, index, _comparer, Bof(Pal.Contents(_entries), index));
            PushEntryIntoBucket(ref entry, index);
            FillStep(b3.Value, Pal.Contents(_buckets), e3.Value, Pal.Contents(_entries), count + 1, index, _comparer);
            Pal.Assert(Keysh(e3.Value, count + 1, index) == keys0.Value);
            Pal.Assert(Pal.Same(e3.Value[index].Key, key));
            Pal.Assert(KeysOf(Pal.Contents(_entries), count + 1) == InsK(Keysh(e3.Value, count + 1, index), index, e3.Value[index].Key));
            Pal.Assert(KeysOf(Pal.Contents(_entries), count + 1) == InsK(keys0.Value, index, key));
            Pal.Assert(Valuesh(e3.Value, count + 1, index) == values0.Value);
            Pal.Assert(Pal.Same(e3.Value[index].Value, value));
            Pal.Assert(ValuesOf(Pal.Contents(_entries), count + 1) == InsV(values0.Value, index, value));
            _count++;
            _version++;

            RehashIfNecessary(collisionCount, entries);

            keyIndex = index;
            Debug.Assert(0 <= keyIndex && keyIndex < _count);

            return true;
        }

        /// <summary>Adds the specified key and value to the dictionary.</summary>
        /// <param name="key">The key of the element to add.</param>
        /// <param name="value">The value of the element to add. The value can be <see langword="null"/> for reference types.</param>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        /// <exception cref="ArgumentException">An element with the same key already exists in the <see cref="OrderedDictionary{TKey, TValue}"/>.</exception>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Throws(typeof(ArgumentException), "OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("!Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), Pal.Old(@this.SpecCount), key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), Pal.Old(@this.SpecCount), value)")]
        public void Add(TKey key, TValue value)
        {
            ArgumentNullException.ThrowIfNull(key);

            TryInsert(index: -1, key, value, InsertionBehavior.ThrowOnExisting, out _);
        }

        /// <summary>Adds the specified key and value to the dictionary if the key doesn't already exist.</summary>
        /// <param name="key">The key of the element to add.</param>
        /// <param name="value">The value of the element to add. The value can be <see langword="null"/> for reference types.</param>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        /// <returns><see langword="true"/> if the key didn't exist and the key and value were added to the dictionary; otherwise, <see langword="false"/>.</returns>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Throws(typeof(ArgumentException), "@this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("Result == !Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(Result, @this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), Pal.Old(@this.SpecCount), key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), Pal.Old(@this.SpecCount), value))")]
        [Ensures("Pal.Implies(!Result, @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues))")]
        public bool TryAdd(TKey key, TValue value) => TryAdd(key, value, out _);

        /// <summary>Adds the specified key and value to the dictionary if the key doesn't already exist.</summary>
        /// <param name="key">The key of the element to add.</param>
        /// <param name="value">The value of the element to add. The value can be <see langword="null"/> for reference types.</param>
        /// <param name="index">The index of the added or existing <paramref name="key"/>. This is always a valid index into the dictionary.</param>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        /// <returns><see langword="true"/> if the key didn't exist and the key and value were added to the dictionary; otherwise, <see langword="false"/>.</returns>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Throws(typeof(ArgumentException), "@this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("Result == !Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(Result, @this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), Pal.Old(@this.SpecCount), key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), Pal.Old(@this.SpecCount), value))")]
        [Ensures("Pal.Implies(!Result, @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues))")]
        [Ensures("Pal.Implies(Result, index == Pal.Old(@this.SpecCount))")]
        [Ensures("Pal.Implies(!Result, 0 <= index && index < @this.SpecCount && index < @this.SpecKeys.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[index], key))")]
        public bool TryAdd(TKey key, TValue value, out int index)
        {
            ArgumentNullException.ThrowIfNull(key);

            return TryInsert(index: -1, key, value, InsertionBehavior.IgnoreInsertion, out index);
        }

        /// <summary>Adds each element of the enumerable to the dictionary.</summary>
        private void AddRange(IEnumerable<KeyValuePair<TKey, TValue>> collection)
        {
            Debug.Assert(collection is not null);

            if (collection is KeyValuePair<TKey, TValue>[] array)
            {
                foreach (KeyValuePair<TKey, TValue> pair in array)
                {
                    Add(pair.Key, pair.Value);
                }
            }
            else
            {
                foreach (KeyValuePair<TKey, TValue> pair in collection)
                {
                    Add(pair.Key, pair.Value);
                }
            }
        }

        /// <summary>Removes all keys and values from the <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        [Ensures("@this.SpecCount == 0")]
        [Ensures("@this.SpecKeys == Pal.EmptySeq<TKey>()")]
        [Ensures("@this.SpecValues == Pal.EmptySeq<TValue>()")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        public void Clear()
        {
            if (_buckets is not null && _count != 0)
            {
                Debug.Assert(_entries is not null);

                Array.Clear(_buckets, 0, _buckets.Length);
                Array.Clear(_entries, 0, _count);
                WfClear(Pal.Contents(_buckets), Pal.Contents(_entries), _comparer);
                _count = 0;
                _version++;
            }
        }

        /// <summary>Determines whether the <see cref="OrderedDictionary{TKey, TValue}"/> contains the specified key.</summary>
        /// <param name="key">The key to locate in the <see cref="OrderedDictionary{TKey, TValue}"/>.</param>
        /// <returns><see langword="true"/> if the <see cref="OrderedDictionary{TKey, TValue}"/> contains an element with the specified key; otherwise, <see langword="false"/>.</returns>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Ensures("Result == OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        public bool ContainsKey(TKey key) => IndexOf(key) >= 0;

        /// <summary>Determines whether the <see cref="OrderedDictionary{TKey, TValue}"/> contains a specific value.</summary>
        /// <param name="value">The value to locate in the <see cref="OrderedDictionary{TKey, TValue}"/>. The value can be null for reference types.</param>
        /// <returns><see langword="true"/> if the <see cref="OrderedDictionary{TKey, TValue}"/> contains an element with the specified value; otherwise, <see langword="false"/>.</returns>
        [Ensures("Result == OrderedDictionary<TKey, TValue>.HasValue(@this.SpecValues, value, @this.SpecCount)")]
        public bool ContainsValue(TValue value)
        {
            int count = _count;

            Entry[]? entries = _entries;
            if (entries is null)
            {
                return false;
            }

            if (typeof(TValue).IsValueType)
            {
                for (int i = 0; i < count; i++)
                {
                    Pal.Invariant(0 <= i && i <= count);
                    Pal.Invariant(!HasValue(ValuesOf(Pal.Contents(entries), count), value, i));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && HasValue(ValuesOf(Pal.Contents(entries), count), value, count)));
                    if (EqualityComparer<TValue>.Default.Equals(value, entries[i].Value))
                    {
                        return true;
                    }
                }
            }
            else
            {
                EqualityComparer<TValue> comparer = EqualityComparer<TValue>.Default;
                for (int i = 0; i < count; i++)
                {
                    Pal.Invariant(0 <= i && i <= count);
                    Pal.Invariant(!HasValue(ValuesOf(Pal.Contents(entries), count), value, i));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && HasValue(ValuesOf(Pal.Contents(entries), count), value, count)));
                    if (comparer.Equals(value, entries[i].Value))
                    {
                        return true;
                    }
                }
            }

            return false;
        }

        /// <summary>Gets the key/value pair at the specified index.</summary>
        /// <param name="index">The zero-based index of the pair to get.</param>
        /// <returns>The element at the specified index.</returns>
        /// <exception cref="ArgumentOutOfRangeException"><paramref name="index"/> is less than 0 or greater than or equal to <see cref="Count"/>.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
        [Ensures("0 <= index && index < @this.SpecCount")]
        [Ensures("index < @this.SpecKeys.Length && index < @this.SpecValues.Length && Pal.Same(Result.Key, @this.SpecKeys[index]) && Pal.Same(Result.Value, @this.SpecValues[index])")]
        public KeyValuePair<TKey, TValue> GetAt(int index)
        {
            if ((uint)index >= (uint)_count)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange();
            }

            Debug.Assert(_entries is not null, "count must be positive, which means we must have entries");

            ref Entry e = ref _entries[index];
            return new(e.Key, e.Value);
        }

        /// <summary>Determines the index of a specific key in the <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        /// <param name="key">The key to locate.</param>
        /// <returns>The index of <paramref name="key"/> if found; otherwise, -1.</returns>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Ensures("-1 <= Result && Result < @this.SpecCount")]
        [Ensures("Implies(Result >= 0, Result < @this.SpecKeys.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[Result], key))")]
        [Ensures("(Result >= 0) == OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public int IndexOf(TKey key)
        {
            ArgumentNullException.ThrowIfNull(key);

            uint _ = 0;
            return IndexOf(key, ref _, ref _);
        }

        [Requires("key != null")]
        [Ensures("-1 <= Result && Result < @this.SpecCount")]
        [Ensures("Implies(Result >= 0, Result < @this.SpecKeys.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[Result], key))")]
        [Ensures("Implies(Result >= 0, OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key))")]
        [Ensures("Implies(Result < 0, !OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key))")]
        [Ensures("outHashCode == OrderedDictionary<TKey, TValue>.HashOf(@this.SpecComparer, key)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        private int IndexOf(TKey key, ref uint outHashCode, ref uint outCollisionCount)
        {
            Debug.Assert(key is not null, "Key nullness should have been validated by caller.");

            uint hashCode;
            uint collisionCount = 0;
            IEqualityComparer<TKey>? comparer = _comparer;

            if (_buckets is null)
            {
                hashCode = (uint)(comparer?.GetHashCode(key) ?? key.GetHashCode());
                collisionCount = 0;
                goto ReturnNotFound;
            }

            int i = -1;
            ref Entry entry = ref Unsafe.NullRef<Entry>();

            Entry[]? entries = _entries;
            Debug.Assert(entries is not null, "expected entries to be is not null");

            if (typeof(TKey).IsValueType && // comparer can only be null for value types; enable JIT to eliminate entire if block for ref types
                comparer is null)
            {
                // ValueType: Devirtualize with EqualityComparer<TKey>.Default intrinsic

                hashCode = (uint)key.GetHashCode();
                Pal.Assert(hashCode == HashOf(_comparer, key));
                SearchStart(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key);
                i = GetBucket(hashCode) - 1; // Value in _buckets is 1-based; subtract 1 from i. We do it here so it fuses with the following conditional.
                Pal.Assert(i == Bucket(Pal.Contents(_buckets), Pal.Contents(entries), _comparer, key) - 1);
                do
                {
                    Pal.Invariant(collisionCount <= (uint)entries.Length);
                    Pal.Invariant(Pal.Returned() == Pal.Broke());
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key, i, collisionCount)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), outHashCode == HashOf(_comparer, key)));
                    Pal.Invariant(Pal.Implies(Pal.Returned() && Pal.Result<int>() < 0, Pal.Result<int>() == -1 && !Mem(_comparer, KeysOf(Pal.Contents(entries), _count), key)));
                    Pal.Invariant(Pal.Implies(Pal.Returned() && Pal.Result<int>() >= 0, Pal.Result<int>() < _count && Pal.Result<int>() < KeysOf(Pal.Contents(entries), _count).Length && KeyEq(_comparer, KeysOf(Pal.Contents(entries), _count)[Pal.Result<int>()], key) && Mem(_comparer, KeysOf(Pal.Contents(entries), _count), key)));
                    Pal.Decreases((uint)entries.Length - collisionCount);
                    // Test in if to drop range check for following array access
                    if ((uint)i >= (uint)entries.Length)
                    {
                        SearchAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key, i, collisionCount);
                        goto ReturnNotFound;
                    }

                    entry = ref entries[i];
                    if (entry.HashCode == hashCode && EqualityComparer<TKey>.Default.Equals(entry.Key, key))
                    {
                        SearchHit(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key, i, collisionCount);
                        goto Return;
                    }

                    SearchStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key, i, collisionCount);
                    i = entry.Next;

                    collisionCount++;
                }
                while (collisionCount <= (uint)entries.Length);

                // The chain of entries forms a loop; which means a concurrent update has happened.
                // Break out of the loop and throw, rather than looping forever.
                goto ConcurrentOperation;
            }
            else
            {
                Debug.Assert(comparer is not null);
                hashCode = (uint)comparer.GetHashCode(key);
                Pal.Assert(hashCode == HashOf(_comparer, key));
                SearchStart(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key);
                i = GetBucket(hashCode) - 1; // Value in _buckets is 1-based; subtract 1 from i. We do it here so it fuses with the following conditional.
                Pal.Assert(i == Bucket(Pal.Contents(_buckets), Pal.Contents(entries), _comparer, key) - 1);
                do
                {
                    Pal.Invariant(collisionCount <= (uint)entries.Length);
                    Pal.Invariant(Pal.Returned() == Pal.Broke());
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key, i, collisionCount)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), outHashCode == HashOf(_comparer, key)));
                    Pal.Invariant(Pal.Implies(Pal.Returned() && Pal.Result<int>() < 0, Pal.Result<int>() == -1 && !Mem(_comparer, KeysOf(Pal.Contents(entries), _count), key)));
                    Pal.Invariant(Pal.Implies(Pal.Returned() && Pal.Result<int>() >= 0, Pal.Result<int>() < _count && Pal.Result<int>() < KeysOf(Pal.Contents(entries), _count).Length && KeyEq(_comparer, KeysOf(Pal.Contents(entries), _count)[Pal.Result<int>()], key) && Mem(_comparer, KeysOf(Pal.Contents(entries), _count), key)));
                    Pal.Decreases((uint)entries.Length - collisionCount);
                    // Test in if to drop range check for following array access
                    if ((uint)i >= (uint)entries.Length)
                    {
                        SearchAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key, i, collisionCount);
                        goto ReturnNotFound;
                    }

                    entry = ref entries[i];
                    if (entry.HashCode == hashCode && comparer.Equals(entry.Key, key))
                    {
                        SearchHit(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key, i, collisionCount);
                        goto Return;
                    }

                    SearchStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _comparer, key, i, collisionCount);
                    i = entry.Next;

                    collisionCount++;
                }
                while (collisionCount <= (uint)entries.Length);

                // The chain of entries forms a loop; which means a concurrent update has happened.
                // Break out of the loop and throw, rather than looping forever.
                goto ConcurrentOperation;
            }

        ReturnNotFound:
            i = -1;
            outCollisionCount = collisionCount;
            goto Return;

        ConcurrentOperation:
            // We examined more entries than are actually in the list, which means there's a cycle
            // that's caused by erroneous concurrent use.
            ThrowHelper.ThrowConcurrentOperation();

        Return:
            outHashCode = hashCode;
            return i;
        }

        /// <summary>Inserts an item into the collection at the specified index.</summary>
        /// <param name="index">The zero-based index at which item should be inserted.</param>
        /// <param name="key">The key to insert.</param>
        /// <param name="value">The value to insert.</param>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        /// <exception cref="ArgumentException">An element with the same key already exists in the <see cref="OrderedDictionary{TKey, TValue}"/>.</exception>
        /// <exception cref="ArgumentOutOfRangeException"><paramref name="index"/> is less than 0 or greater than <see cref="Count"/>.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index > @this.SpecCount")]
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Throws(typeof(ArgumentException), "OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("0 <= index && index <= Pal.Old(@this.SpecCount) && !Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), index, key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), index, value)")]
        public void Insert(int index, TKey key, TValue value)
        {
            if ((uint)index > (uint)_count)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange();
            }

            ArgumentNullException.ThrowIfNull(key);

            TryInsert(index, key, value, InsertionBehavior.ThrowOnExisting, out _);
        }

        /// <summary>Removes the value with the specified key from the <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        /// <param name="key">The key of the element to remove.</param>
        /// <returns><see langword="true"/> if the element is successfully found and removed; otherwise, <see langword="false"/>.</returns>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Ensures("Result == Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(!Result, @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues))")]
        [Ensures("Pal.Implies(Result, @this.SpecCount == Pal.Old(@this.SpecCount) - 1)")]
        [Ensures("Pal.Implies(Result, Pal.Exists((int i) => 0 <= i && i < Pal.Old(@this.SpecCount) && i < Pal.Old(@this.SpecKeys).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, Pal.Old(@this.SpecKeys)[i], key) && @this.SpecKeys == OrderedDictionary<TKey, TValue>.DelK(Pal.Old(@this.SpecKeys), i) && @this.SpecValues == OrderedDictionary<TKey, TValue>.DelV(Pal.Old(@this.SpecValues), i)))")]
        public bool Remove(TKey key) => Remove(key, out _);

        /// <summary>Removes the value with the specified key from the <see cref="OrderedDictionary{TKey, TValue}"/> and copies the element to the value parameter.</summary>
        /// <param name="key">The key of the element to remove.</param>
        /// <param name="value">The removed element.</param>
        /// <returns><see langword="true"/> if the element is successfully found and removed; otherwise, <see langword="false"/>.</returns>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Ensures("Result == Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(!Result, @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues))")]
        [Ensures("Pal.Implies(Result, @this.SpecCount == Pal.Old(@this.SpecCount) - 1)")]
        [Ensures("Pal.Implies(Result, Pal.Exists((int i) => 0 <= i && i < Pal.Old(@this.SpecCount) && i < Pal.Old(@this.SpecKeys).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, Pal.Old(@this.SpecKeys)[i], key) && @this.SpecKeys == OrderedDictionary<TKey, TValue>.DelK(Pal.Old(@this.SpecKeys), i) && @this.SpecValues == OrderedDictionary<TKey, TValue>.DelV(Pal.Old(@this.SpecValues), i) && i < Pal.Old(@this.SpecValues).Length && Pal.Same(value, Pal.Old(@this.SpecValues)[i])))")]
        public bool Remove(TKey key, [MaybeNullWhen(false)] out TValue value)
        {
            ArgumentNullException.ThrowIfNull(key);

            // Find the key.
            int index = IndexOf(key);
            if (index >= 0)
            {
                // It exists. Remove it.
                Debug.Assert(_entries is not null);

                value = _entries[index].Value;
                RemoveAt(index);

                return true;
            }

            value = default;
            return false;
        }

        /// <summary>Removes the key/value pair at the specified index.</summary>
        /// <param name="index">The zero-based index of the item to remove.</param>
        /// <exception cref="ArgumentOutOfRangeException"><paramref name="index"/> is less than 0 or greater than or equal to <see cref="Count"/>.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
        [Ensures("0 <= index && index < Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) - 1")]
        [Ensures("@this.SpecKeys == OrderedDictionary<TKey, TValue>.DelK(Pal.Old(@this.SpecKeys), index)")]
        [Ensures("@this.SpecValues == OrderedDictionary<TKey, TValue>.DelV(Pal.Old(@this.SpecValues), index)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        public void RemoveAt(int index)
        {
            int count = _count;
            if ((uint)index >= (uint)count)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange();
            }

            Ghost<Seq<TKey>> keys0 = KeysOf(Pal.Contents(_entries), count);
            Ghost<Seq<TValue>> values0 = ValuesOf(Pal.Contents(_entries), count);
            Ghost<int> capacity0 = Pal.Contents(_entries).Length;
            KeyshDel(Pal.Contents(_entries), count, index);

            // Remove from the associated bucket chain the entry that lives at the specified index.
            RemoveEntryFromBucket(index);

            // Shift down all entries above this one, and fix up the bucket chains to reflect the new indices.
            Entry[]? entries = _entries;
            Debug.Assert(entries is not null);
            for (int i = index + 1; i < count; i++)
            {
                Pal.Invariant(index + 1 <= i && i <= count && _count == count);
                Pal.Invariant(entries == _entries && _buckets != null && _entries != null);
                Pal.Invariant(Pal.Contents(_buckets).Length == Pal.Contents(_entries).Length && count <= Pal.Contents(_entries).Length);
                Pal.Invariant(Pal.Contents(_entries).Length == capacity0.Value);
                Pal.Invariant(IntPtr.Size != 8 || _fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)Pal.Contents(_buckets).Length));
                Pal.Invariant(Wfm(Pal.Contents(_buckets), Pal.Contents(_entries), count, i - 1, _comparer));
                Pal.Invariant(Keysh(Pal.Contents(_entries), count, i - 1) == DelK(keys0.Value, index));
                Pal.Invariant(Valuesh(Pal.Contents(_entries), count, i - 1) == DelV(values0.Value, index));
                Ghost<Seq<Entry>> e1 = Pal.Contents(_entries);
                entries[i - 1] = entries[i];
                HoleEq(Pal.Contents(_buckets), e1.Value, Pal.Contents(_entries), count, i - 1, _comparer);
                UpdateBucketIndex(i, shiftAmount: -1);
            }

            Ghost<Seq<Entry>> e2 = Pal.Contents(_entries);
            entries[--_count] = default;
            CloseOk(Pal.Contents(_buckets), e2.Value, Pal.Contents(_entries), count, _comparer);
            _version++;
        }

        /// <summary>Sets the value for the key at the specified index.</summary>
        /// <param name="index">The zero-based index at which to set the value.</param>
        /// <param name="value">The value to store at the specified index.</param>
        /// <exception cref="ArgumentOutOfRangeException"><paramref name="index"/> is less than 0 or greater than or equal to <see cref="Count"/>.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
        [Ensures("0 <= index && index < Pal.Old(@this.SpecCount) && index < Pal.Old(@this.SpecValues).Length")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecKeys == Pal.Old(@this.SpecKeys)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.SpecValues == Pal.SetAt(Pal.Old(@this.SpecValues), index, value)")]
        public void SetAt(int index, TValue value)
        {
            if ((uint)index >= (uint)_count)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange();
            }

            Debug.Assert(_entries is not null);

            WfSetValue(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _comparer, index, value);
            _entries[index].Value = value;
        }

        /// <summary>Sets the key/value pair at the specified index.</summary>
        /// <param name="index">The zero-based index at which to set the key/value pair.</param>
        /// <param name="key">The key to store at the specified index.</param>
        /// <param name="value">The value to store at the specified index.</param>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        /// <exception cref="ArgumentException">An element with the same key already exists at an index different to <paramref name="index"/>.</exception>
        /// <exception cref="ArgumentOutOfRangeException"><paramref name="index"/> is less than 0 or greater than or equal to <see cref="Count"/>.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Throws(typeof(ArgumentException), "OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        [Ensures("0 <= index && index < Pal.Old(@this.SpecCount) && index < Pal.Old(@this.SpecKeys).Length && index < Pal.Old(@this.SpecValues).Length")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecComparer == Pal.Old(@this.SpecComparer) && @this.SpecCapacity == Pal.Old(@this.SpecCapacity)")]
        [Ensures("@this.SpecValues == Pal.SetAt(Pal.Old(@this.SpecValues), index, value)")]
        [Ensures("Pal.Implies(0 <= index && index < Pal.Old(@this.SpecKeys).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, key, Pal.Old(@this.SpecKeys)[index]), @this.SpecKeys == Pal.Old(@this.SpecKeys))")]
        [Ensures("Pal.Implies(0 <= index && index < Pal.Old(@this.SpecKeys).Length && !OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, key, Pal.Old(@this.SpecKeys)[index]), @this.SpecKeys == Pal.SetAt(Pal.Old(@this.SpecKeys), index, key))")]
        public void SetAt(int index, TKey key, TValue value)
        {
            if ((uint)index >= (uint)_count)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange();
            }

            ArgumentNullException.ThrowIfNull(key);

            Debug.Assert(_entries is not null);
            Ghost<Seq<TKey>> keys0 = KeysOf(Pal.Contents(_entries), _count);
            Ghost<Seq<TValue>> values0 = ValuesOf(Pal.Contents(_entries), _count);
            KeyshDel(Pal.Contents(_entries), _count, index);
            ref Entry e = ref _entries[index];

            // If the key matches the one that's already in that slot, just update the value.
            if (typeof(TKey).IsValueType && _comparer is null)
            {
                if (EqualityComparer<TKey>.Default.Equals(key, e.Key))
                {
                    WfSetValue(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _comparer, index, value);
                    e.Value = value;
                    return;
                }
            }
            else
            {
                Debug.Assert(_comparer is not null);
                if (_comparer.Equals(key, e.Key))
                {
                    WfSetValue(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _comparer, index, value);
                    e.Value = value;
                    return;
                }
            }

            // The key doesn't match that index. If it exists elsewhere in the collection, fail.
            uint hashCode = 0, collisionCount = 0;
            if (IndexOf(key, ref hashCode, ref collisionCount) >= 0)
            {
                ThrowHelper.ThrowDuplicateKey(key);
            }

            // The key doesn't exist in the collection. Update the key and value, but also update
            // the bucket chains, as the new key may not hash to the same bucket as the old key
            // (we could check for this, but in a properly balanced dictionary the chances should
            // be low for a match, so it's not worth it).
            RemoveEntryFromBucket(index);
            Ghost<Seq<Entry>> e2 = Pal.Contents(_entries);
            e.HashCode = hashCode;
            e.Key = key;
            e.Value = value;
            HoleEq(Pal.Contents(_buckets), e2.Value, Pal.Contents(_entries), _count, index, _comparer);
            Ghost<Seq<int>> b3 = Pal.Contents(_buckets);
            Ghost<Seq<Entry>> e3 = Pal.Contents(_entries);
            WfmHead(Pal.Contents(_buckets), Pal.Contents(_entries), _count, index, _comparer, Bof(Pal.Contents(_entries), index));
            PushEntryIntoBucket(ref e, index);
            FillStep(b3.Value, Pal.Contents(_buckets), e3.Value, Pal.Contents(_entries), _count, index, _comparer);
            InsDelK(keys0.Value, index, key);
            InsDelV(values0.Value, index, value);

            _version++;

            RehashIfNecessary(collisionCount, _entries);
        }

        /// <summary>Ensures that the dictionary can hold up to <paramref name="capacity"/> entries without resizing.</summary>
        /// <param name="capacity">The desired minimum capacity of the dictionary. The actual capacity provided may be larger.</param>
        /// <returns>The new capacity of the dictionary.</returns>
        /// <exception cref="ArgumentOutOfRangeException"><paramref name="capacity"/> is negative.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Result == @this.SpecCapacity && Result >= capacity && Result >= Pal.Old(@this.SpecCapacity)")]
        [Ensures("Pal.Implies(capacity <= Pal.Old(@this.SpecCapacity), @this.SpecCapacity == Pal.Old(@this.SpecCapacity))")]
        public int EnsureCapacity(int capacity)
        {
            ThrowIfNegative(capacity);

            if (Capacity < capacity)
            {
                if (_buckets is null)
                {
                    EnsureBucketsAndEntriesInitialized(capacity);
                }
                else
                {
                    Resize(HashHelpers.GetPrime(capacity));
                }

                _version++;
            }

            return Capacity;
        }

        /// <summary>Sets the capacity of this dictionary to what it would be if it had been originally initialized with all its entries.</summary>
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCount <= @this.SpecCapacity && @this.SpecCapacity <= Pal.Old(@this.SpecCapacity)")]
        public void TrimExcess() => TrimExcess(_count);

        /// <summary>Sets the capacity of this dictionary to hold up a specified number of entries without resizing.</summary>
        /// <param name="capacity">The desired capacity to which to shrink the dictionary.</param>
        /// <exception cref="ArgumentOutOfRangeException"><paramref name="capacity"/> is less than <see cref="Count"/>.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < @this.SpecCount")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCount <= @this.SpecCapacity && @this.SpecCapacity <= Pal.Old(@this.SpecCapacity)")]
        public void TrimExcess(int capacity)
        {
            ThrowIfLessThan(capacity, Count);

            int currentCapacity = _entries?.Length ?? 0;
            capacity = HashHelpers.GetPrime(capacity);
            if (capacity < currentCapacity)
            {
                Resize(capacity);
            }
        }

        /// <summary>Gets the value associated with the specified key.</summary>
        /// <param name="key">The key of the value to get.</param>
        /// <param name="value">
        /// When this method returns, contains the value associated with the specified key, if the key is found;
        /// otherwise, the default value for the type of the value parameter.
        /// </param>
        /// <returns><see langword="true"/> if the <see cref="OrderedDictionary{TKey, TValue}"/> contains an element with the specified key; otherwise, <see langword="false"/>.</returns>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Ensures("Result == OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        [Ensures("Pal.Implies(Result, Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], key) && Pal.Same(value, @this.SpecValues[i])))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public bool TryGetValue(TKey key, [MaybeNullWhen(false)] out TValue value) => TryGetValue(key, out value, out _);

        /// <summary>Gets the value associated with the specified key.</summary>
        /// <param name="key">The key of the value to get.</param>
        /// <param name="value">
        /// When this method returns, contains the value associated with the specified key, if the key is found;
        /// otherwise, the default value for the type of the value parameter.
        /// </param>
        /// <param name="index">The index of <paramref name="key"/> if found; otherwise, -1.</param>
        /// <returns><see langword="true"/> if the <see cref="OrderedDictionary{TKey, TValue}"/> contains an element with the specified key; otherwise, <see langword="false"/>.</returns>
        /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Ensures("Result == OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        [Ensures("Result ? 0 <= index && index < @this.SpecCount && index < @this.SpecKeys.Length && index < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[index], key) && Pal.Same(value, @this.SpecValues[index]) : index == -1")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        public bool TryGetValue(TKey key, [MaybeNullWhen(false)] out TValue value, out int index)
        {
            ArgumentNullException.ThrowIfNull(key);

            // Find the key.
            index = IndexOf(key);
            if (index >= 0)
            {
                // It exists. Return its value.
                Debug.Assert(_entries is not null);
                value = _entries[index].Value;
                return true;
            }

            value = default;
            return false;
        }

        /// <summary>Pushes the entry into its bucket.</summary>
        /// <remarks>
        /// The bucket is a linked list by index into the <see cref="_entries"/> array.
        /// The new entry's <see cref="Entry.Next"/> is set to the bucket's current
        /// head, and then the new entry is made the new head.
        /// </remarks>
        [Open]
        [Requires("@this._buckets != null && Pal.Contents(@this._buckets).Length > 0 && Pal.Contents(@this._buckets).Length <= int.MaxValue")]
        [Requires("IntPtr.Size != 8 || @this._fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)Pal.Contents(@this._buckets).Length)")]
        [Requires("0 <= entryIndex && entryIndex < Pal.Contents(@this._buckets).Length")]
        [Requires("Pal.Contents(@this._buckets)[(int)(entry.HashCode % (uint)Pal.Contents(@this._buckets).Length)] >= 0")]
        [Ensures("Pal.Contents(@this._buckets).Length == Pal.Old(Pal.Contents(@this._buckets)).Length")]
        [Ensures("Pal.Contents(@this._buckets)[(int)(entry.HashCode % (uint)Pal.Contents(@this._buckets).Length)] == entryIndex + 1")]
        [Ensures("Pal.Forall((int b) => Pal.Implies(0 <= b && b < Pal.Contents(@this._buckets).Length && b != (int)(entry.HashCode % (uint)Pal.Contents(@this._buckets).Length), Pal.Contents(@this._buckets)[b] == Pal.Old(Pal.Contents(@this._buckets))[b]))")]
        [Ensures("entry.Next == Pal.Old(Pal.Contents(@this._buckets))[(int)(entry.HashCode % (uint)Pal.Contents(@this._buckets).Length)] - 1")]
        [Ensures("entry.HashCode == Pal.Old(entry.HashCode) && entry.Key == Pal.Old(entry.Key) && entry.Value == Pal.Old(entry.Value)")]
        [Ensures("Pal.Contents(@this._entries) == Pal.Old(Pal.Contents(@this._entries))")]
        private void PushEntryIntoBucket(ref Entry entry, int entryIndex)
        {
            ref int bucket = ref GetBucket(entry.HashCode);
            entry.Next = bucket - 1;
            bucket = entryIndex + 1;
        }

        /// <summary>Removes an entry from its bucket.</summary>
        [Open]
        [Requires("@this._buckets != null && @this._entries != null")]
        [Requires("Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length && Pal.Contents(@this._entries).Length <= int.MaxValue")]
        [Requires("IntPtr.Size != 8 || @this._fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)Pal.Contents(@this._buckets).Length)")]
        [Requires("0 <= entryIndex && entryIndex < @this._count && @this._count <= Pal.Contents(@this._entries).Length")]
        [Requires("OrderedDictionary<TKey, TValue>.Wf(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count, @this._comparer)")]
        [Ensures("Pal.Contents(@this._buckets).Length == Pal.Old(Pal.Contents(@this._buckets)).Length && Pal.Contents(@this._entries).Length == Pal.Old(Pal.Contents(@this._entries)).Length")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wfm(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count, entryIndex, @this._comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Keysh(Pal.Contents(@this._entries), @this._count, entryIndex) == Pal.Old(OrderedDictionary<TKey, TValue>.Keysh(Pal.Contents(@this._entries), @this._count, entryIndex))")]
        [Ensures("OrderedDictionary<TKey, TValue>.Valuesh(Pal.Contents(@this._entries), @this._count, entryIndex) == Pal.Old(OrderedDictionary<TKey, TValue>.Valuesh(Pal.Contents(@this._entries), @this._count, entryIndex))")]
        private void RemoveEntryFromBucket(int entryIndex)
        {
            // We're only calling this method if there's an entry to be removed, in which case
            // entries must have been initialized.
            Entry[]? entries = _entries;
            Debug.Assert(entries is not null);

            // Get the entry to be removed and the associated bucket.
            Entry entry = entries[entryIndex];
            ref int bucket = ref GetBucket(entry.HashCode);
            Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
            Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
            Ghost<int> length0 = entries.Length;
            WfNext(Pal.Contents(_buckets), Pal.Contents(entries), _count, entryIndex, _comparer);

            if (bucket == entryIndex + 1)
            {
                // If the entry was at the head of its bucket list, to remove it from the list we
                // simply need to update the next entry in the list to be the new head.
                bucket = entry.Next + 1;
                UnlinkOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), _count, entryIndex, -1, 0, _comparer);
            }
            else
            {
                // The entry wasn't the head of the list. Walk the chain until we find the entry,
                // updating the previous entry's Next to point to this entry's Next.
                WfPredStart(Pal.Contents(_buckets), Pal.Contents(entries), _count, entryIndex, _comparer);
                PredRange(Pal.Contents(_buckets), Pal.Contents(entries), _count, -1, entryIndex, Pal.Contents(_buckets)[Bof(Pal.Contents(entries), entryIndex)] - 1, 0);
                int i = bucket - 1;
                int collisionCount = 0;
                while (true)
                {
                    Pal.Invariant(entries.Length == length0.Value && Pal.Contents(_buckets).Length == length0.Value);
                    Pal.Invariant(0 <= collisionCount);
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.Contents(_buckets) == buckets0.Value && Pal.Contents(entries) == entries0.Value));
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), Pred(Pal.Contents(_buckets), Pal.Contents(entries), _count, -1, entryIndex, i, collisionCount)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Wfm(Pal.Contents(_buckets), Pal.Contents(entries), _count, entryIndex, _comparer)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Keysh(Pal.Contents(entries), _count, entryIndex) == Keysh(entries0.Value, _count, entryIndex)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Valuesh(Pal.Contents(entries), _count, entryIndex) == Valuesh(entries0.Value, _count, entryIndex)));
                    Pal.Decreases(length0.Value - collisionCount);
                    PredRange(Pal.Contents(_buckets), Pal.Contents(entries), _count, -1, entryIndex, i, collisionCount);
                    ref Entry e = ref entries[i];
                    if (e.Next == entryIndex)
                    {
                        e.Next = entry.Next;
                        UnlinkOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), _count, entryIndex, i, collisionCount, _comparer);
                        return;
                    }

                    PredStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, -1, entryIndex, i, collisionCount);
                    i = e.Next;

                    if (++collisionCount > entries.Length)
                    {
                        // We examined more entries than are actually in the list, which means there's a cycle
                        // that's caused by erroneous concurrent use.
                        ThrowHelper.ThrowConcurrentOperation();
                    }
                }
            }
        }

        /// <summary>
        /// Updates the bucket chain containing the specified entry (by index) to shift indices
        /// by the specified amount.
        /// </summary>
        /// <param name="entryIndex">The index of the target entry.</param>
        /// <param name="shiftAmount">
        /// 1 if this is part of an insert and the values are being shifted one higher.
        /// -1 if this is part of a remove and the values are being shifted one lower.
        /// </param>
        [Open]
        [Requires("@this._buckets != null && @this._entries != null")]
        [Requires("Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length && Pal.Contents(@this._entries).Length <= int.MaxValue")]
        [Requires("IntPtr.Size != 8 || @this._fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)Pal.Contents(@this._buckets).Length)")]
        [Requires("shiftAmount == 1 || shiftAmount == -1")]
        [Requires("0 <= entryIndex && entryIndex < @this._count + (shiftAmount + 1) / 2")]
        [Requires("OrderedDictionary<TKey, TValue>.Wfm(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count + (shiftAmount + 1) / 2, entryIndex + shiftAmount, @this._comparer)")]
        [Requires("OrderedDictionary<TKey, TValue>.Copied(Pal.Contents(@this._entries), entryIndex + shiftAmount, entryIndex)")]
        [Ensures("Pal.Contents(@this._buckets).Length == Pal.Old(Pal.Contents(@this._buckets)).Length && Pal.Contents(@this._entries).Length == Pal.Old(Pal.Contents(@this._entries)).Length")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wfm(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count + (shiftAmount + 1) / 2, entryIndex, @this._comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Keysh(Pal.Contents(@this._entries), @this._count + (shiftAmount + 1) / 2, entryIndex) == Pal.Old(OrderedDictionary<TKey, TValue>.Keysh(Pal.Contents(@this._entries), @this._count + (shiftAmount + 1) / 2, entryIndex + shiftAmount))")]
        [Ensures("OrderedDictionary<TKey, TValue>.Valuesh(Pal.Contents(@this._entries), @this._count + (shiftAmount + 1) / 2, entryIndex) == Pal.Old(OrderedDictionary<TKey, TValue>.Valuesh(Pal.Contents(@this._entries), @this._count + (shiftAmount + 1) / 2, entryIndex + shiftAmount))")]
        private void UpdateBucketIndex(int entryIndex, int shiftAmount)
        {
            Debug.Assert(shiftAmount is 1 or -1);

            Entry[]? entries = _entries;
            Debug.Assert(entries is not null);

            Entry entry = entries[entryIndex];
            ref int bucket = ref GetBucket(entry.HashCode);
            Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
            Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
            Ghost<int> m = _count + (shiftAmount + 1) / 2;
            Ghost<int> length0 = entries.Length;

            if (bucket == entryIndex + 1)
            {
                // If the entry was at the head of its bucket list, the only thing that needs to be updated
                // is the bucket head value itself, since no other entries' Next will be referencing this node.
                bucket += shiftAmount;
                MoveOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), m.Value, entryIndex + shiftAmount, entryIndex, -1, 0, _comparer);
            }
            else
            {
                // The entry wasn't the head of the list. Walk the chain until we find the entry, updating
                // the previous entry's Next that's pointing to the target entry.
                WfmPredStart(Pal.Contents(_buckets), Pal.Contents(entries), m.Value, entryIndex + shiftAmount, entryIndex, _comparer);
                WfmHead(Pal.Contents(_buckets), Pal.Contents(entries), m.Value, entryIndex + shiftAmount, _comparer, Bof(Pal.Contents(entries), entryIndex));
                int i = bucket - 1;
                int collisionCount = 0;
                while (true)
                {
                    Pal.Invariant(entries.Length == length0.Value && Pal.Contents(_buckets).Length == length0.Value);
                    Pal.Invariant(0 <= collisionCount);
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.Contents(_buckets) == buckets0.Value && Pal.Contents(entries) == entries0.Value));
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), Pred(Pal.Contents(_buckets), Pal.Contents(entries), m.Value, entryIndex + shiftAmount, entryIndex, i, collisionCount)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Wfm(Pal.Contents(_buckets), Pal.Contents(entries), m.Value, entryIndex, _comparer)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Keysh(Pal.Contents(entries), m.Value, entryIndex) == Keysh(entries0.Value, m.Value, entryIndex + shiftAmount)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Valuesh(Pal.Contents(entries), m.Value, entryIndex) == Valuesh(entries0.Value, m.Value, entryIndex + shiftAmount)));
                    Pal.Decreases(length0.Value - collisionCount);
                    PredRange(Pal.Contents(_buckets), Pal.Contents(entries), m.Value, entryIndex + shiftAmount, entryIndex, i, collisionCount);
                    ref Entry e = ref entries[i];
                    if (e.Next == entryIndex)
                    {
                        e.Next += shiftAmount;
                        MoveOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), m.Value, entryIndex + shiftAmount, entryIndex, i, collisionCount, _comparer);
                        return;
                    }

                    PredStep(Pal.Contents(_buckets), Pal.Contents(entries), m.Value, entryIndex + shiftAmount, entryIndex, i, collisionCount);

                    i = e.Next;

                    if (++collisionCount > entries.Length)
                    {
                        // We examined more entries than are actually in the list, which means there's a cycle
                        // that's caused by erroneous concurrent use.
                        ThrowHelper.ThrowConcurrentOperation();
                    }
                }
            }
        }

        /// <summary>
        /// Checks to see whether the collision count that occurred during lookup warrants upgrading to a non-randomized comparer,
        /// and does so if necessary.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        [SuppressMessage("Performance", "CA1822:Mark members as static", Justification = "Is no-op in certain targets")]
        private void RehashIfNecessary(uint collisionCount, Entry[] entries)
        {
#if SYSTEM_COLLECTIONS
            // If we exceeded the hash collision threshold and we're using a randomized comparer, rehash.
            // This is only ever done for string keys, so we can optimize it all away for value type keys.
            if (!typeof(TKey).IsValueType &&
                collisionCount > HashHelpers.HashCollisionThreshold &&
                _comparer is NonRandomizedStringEqualityComparer)
            {
                // Switch to a randomized comparer and rehash.
                Resize(entries.Length, forceNewHashCodes: true);
            }
#endif
        }

        /// <summary>Grow or shrink <see cref="_buckets"/> and <see cref="_entries"/> to the specified capacity.</summary>
        [MemberNotNull(nameof(_buckets))]
        [MemberNotNull(nameof(_entries))]
        [Open]
        [Requires("0 <= @this._count && @this._count <= newSize && newSize > 0 && (!forceNewHashCodes || !typeof(TKey).IsValueType)")]
        [Requires("(@this._buckets == null) == (@this._entries == null) && (@this._entries != null || @this._count == 0)")]
        [Requires("Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length && @this._count <= Pal.Contents(@this._entries).Length")]
        [Requires("Pal.Implies(@this._buckets != null, OrderedDictionary<TKey, TValue>.Wf(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count, @this._comparer))")]
        [Ensures("@this._buckets != null && @this._entries != null")]
        [Ensures("Pal.Contents(@this._buckets).Length == newSize && Pal.Contents(@this._entries).Length == newSize")]
        [Ensures("IntPtr.Size != 8 || @this._fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)Pal.Contents(@this._buckets).Length)")]
        [Ensures("OrderedDictionary<TKey, TValue>.Wf(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count, @this._comparer)")]
        [Ensures("OrderedDictionary<TKey, TValue>.KeysOf(Pal.Contents(@this._entries), @this._count) == Pal.Old(OrderedDictionary<TKey, TValue>.KeysOf(Pal.Contents(@this._entries), @this._count))")]
        [Ensures("OrderedDictionary<TKey, TValue>.ValuesOf(Pal.Contents(@this._entries), @this._count) == Pal.Old(OrderedDictionary<TKey, TValue>.ValuesOf(Pal.Contents(@this._entries), @this._count))")]
        [Rlimit(4)]
        private void Resize(int newSize, bool forceNewHashCodes = false)
        {
            Debug.Assert(!forceNewHashCodes || !typeof(TKey).IsValueType, "Value types never rehash.");
            Debug.Assert(newSize >= _count, "The requested size must accommodate all of the current elements.");

            // Create the new arrays. We allocate both prior to storing either; in case one of the allocation fails,
            // we want to avoid corrupting the data structure.
            int[] newBuckets = new int[newSize];
            Entry[] newEntries = new Entry[newSize];
            if (IntPtr.Size == 8)
            {
                // Any time the capacity changes, that impacts the divisor of modulo operations,
                // and we need to update our fast modulo multiplier.
                _fastModMultiplier = HashHelpers.GetFastModMultiplier((uint)newSize);
            }

            // Copy the existing entries to the new entries array.
            int count = _count;
            Ghost<Seq<int>> oldBuckets = Pal.Contents(_buckets);
            Ghost<Seq<Entry>> oldEntries = Pal.Contents(_entries);
            if (_entries is not null)
            {
                Array.Copy(_entries, newEntries, count);
            }
            SameKvhCopy(Pal.Contents(newEntries), oldEntries.Value, count);

#if SYSTEM_COLLECTIONS
            // If we're being asked to upgrade to a non-randomized comparer due to too many collisions, do so.
            if (!typeof(TKey).IsValueType && forceNewHashCodes)
            {
                // Store the original randomized comparer instead of the non-randomized one.
                Debug.Assert(_comparer is NonRandomizedStringEqualityComparer);
                IEqualityComparer<TKey> comparer = _comparer = (IEqualityComparer<TKey>)((NonRandomizedStringEqualityComparer)_comparer).GetUnderlyingEqualityComparer();
                Debug.Assert(_comparer is not null);
                Debug.Assert(_comparer is not NonRandomizedStringEqualityComparer);

                // Update all of the entries' hash codes based on the new comparer.
                for (int i = 0; i < count; i++)
                {
                    newEntries[i].HashCode = (uint)comparer.GetHashCode(newEntries[i].Key);
                }
            }
#endif

            // Now publish the buckets array. It's necessary to do this prior to the below loop,
            // as PushEntryIntoBucket will be populating _buckets.
            _buckets = newBuckets;
            WfClear(Pal.Contents(_buckets), Pal.Contents(newEntries), _comparer);

            // Populate the buckets.
            for (int i = 0; i < count; i++)
            {
                Pal.Invariant(0 <= i && i <= count && count == _count && count <= newSize);
                Pal.Invariant(_buckets != null && Pal.Contents(_buckets).Length == newSize && Pal.Contents(newEntries).Length == newSize);
                Pal.Invariant(IntPtr.Size != 8 || _fastModMultiplier == System.Collections.HashHelpers.Multiplier((uint)Pal.Contents(_buckets).Length));
                Pal.Invariant(Wf(Pal.Contents(_buckets), Pal.Contents(newEntries), i, _comparer));
                Pal.Invariant(SameKvh(Pal.Contents(newEntries), oldEntries.Value, count));
                Pal.Invariant(Pal.Implies(count > 0, Wf(oldBuckets.Value, oldEntries.Value, count, _comparer)));
                Ghost<Seq<int>> bs0 = Pal.Contents(_buckets);
                Ghost<Seq<Entry>> es0 = Pal.Contents(newEntries);
                WfHead(Pal.Contents(_buckets), Pal.Contents(newEntries), i, _comparer, Bof(Pal.Contents(newEntries), i));
                PushEntryIntoBucket(ref newEntries[i], i);
                PushStep(bs0.Value, Pal.Contents(_buckets), es0.Value, Pal.Contents(newEntries), oldBuckets.Value, oldEntries.Value, i, count, _comparer);
            }
            ResizePairs(Pal.Contents(newEntries), oldEntries.Value, count);

            _entries = newEntries;
        }

        /// <summary>Gets the bucket assigned to the specified hash code.</summary>
        /// <remarks>
        /// Buckets are 1-based. This is so that the default initialized value of 0
        /// maps to -1 and is usable as a sentinel.
        /// </remarks>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private ref int GetBucket(uint hashCode)
        {
            int[]? buckets = _buckets;
            Debug.Assert(buckets is not null);

            if (IntPtr.Size == 8)
            {
                return ref buckets[HashHelpers.FastMod(hashCode, (uint)buckets.Length, _fastModMultiplier)];
            }
            else
            {
                return ref buckets[(uint)hashCode % buckets.Length];
            }
        }

        /// <summary>Returns an enumerator that iterates through the <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        /// <returns>A <see cref="OrderedDictionary{TKey, TValue}.Enumerator"/> structure for the <see cref="OrderedDictionary{TKey, TValue}"/>.</returns>
        [Ensures("ReferenceEquals(Result._dictionary, @this) && Result._version == @this.SpecVersion && Result._index == 0")]
        [Ensures("!Result._useDictionaryEntry")]
        public Enumerator GetEnumerator() => new(this, useDictionaryEntry: false);

        /// <inheritdoc/>
        [Ensures("Pal.Implies(@this.SpecCount != 0, Pal.Exists((OrderedDictionary<TKey, TValue>.Enumerator e) => Pal.Boxes(Result, e) && " +
            "ReferenceEquals(e._dictionary, @this) && e._version == @this.SpecVersion && e._index == 0 && !e._useDictionaryEntry))")]
        IEnumerator<KeyValuePair<TKey, TValue>> IEnumerable<KeyValuePair<TKey, TValue>>.GetEnumerator() =>
            Count == 0 ? EnumerableHelpers.GetEmptyEnumerator<KeyValuePair<TKey, TValue>>() :
            GetEnumerator();

        /// <inheritdoc/>
        IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<KeyValuePair<TKey, TValue>>)this).GetEnumerator();

        /// <inheritdoc/>
        [Ensures("Pal.Exists((OrderedDictionary<TKey, TValue>.Enumerator e) => Pal.Boxes(Result, e) && " +
            "ReferenceEquals(e._dictionary, @this) && e._version == @this.SpecVersion && e._index == 0 && e._useDictionaryEntry)")]
        IDictionaryEnumerator IDictionary.GetEnumerator() => new Enumerator(this, useDictionaryEntry: true);

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(item.Key)")]
        [Ensures("-1 <= Result && Result < @this.SpecCount")]
        [Ensures("Pal.Implies(Result >= 0, Result < @this.SpecKeys.Length && Result < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[Result], item.Key) && Pal.DefaultEquals(item.Value, @this.SpecValues[Result]))")]
        // IndexOf(TKey) finds *a* matching key (§33 Findings), so a miss is either no key or a key whose value differs.
        [Ensures("Pal.Implies(Result < 0, !OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, item.Key) || Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], item.Key) && !Pal.DefaultEquals(item.Value, @this.SpecValues[i])))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        int IList<KeyValuePair<TKey, TValue>>.IndexOf(KeyValuePair<TKey, TValue> item)
        {
            ArgumentNullException.ThrowIfNull(item.Key, nameof(item));

            int index = IndexOf(item.Key);
            if (index >= 0)
            {
                Debug.Assert(_entries is not null);
                if (EqualityComparer<TValue>.Default.Equals(item.Value, _entries[index].Value))
                {
                    return index;
                }
            }

            return -1;
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index > @this.SpecCount")]
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(item.Key)")]
        [Throws(typeof(ArgumentException), "OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, item.Key) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("0 <= index && index <= Pal.Old(@this.SpecCount) && !Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, item.Key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), index, item.Key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), index, item.Value)")]
        void IList<KeyValuePair<TKey, TValue>>.Insert(int index, KeyValuePair<TKey, TValue> item) => Insert(index, item.Key, item.Value);

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(item.Key)")]
        [Throws(typeof(ArgumentException), "OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, item.Key) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("!Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, item.Key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), Pal.Old(@this.SpecCount), item.Key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), Pal.Old(@this.SpecCount), item.Value)")]
        void ICollection<KeyValuePair<TKey, TValue>>.Add(KeyValuePair<TKey, TValue> item) => Add(item.Key, item.Value);

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(item.Key)")]
        [Ensures("Pal.Implies(Result, Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], item.Key) && Pal.DefaultEquals(@this.SpecValues[i], item.Value)))")]
        [Ensures("Pal.Implies(!Result, !OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, item.Key) || Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], item.Key) && !Pal.DefaultEquals(@this.SpecValues[i], item.Value)))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        bool ICollection<KeyValuePair<TKey, TValue>>.Contains(KeyValuePair<TKey, TValue> item)
        {
            ArgumentNullException.ThrowIfNull(item.Key, nameof(item));

            return
                TryGetValue(item.Key, out TValue? value) &&
                EqualityComparer<TValue>.Default.Equals(value, item.Value);
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentOutOfRangeException), "arrayIndex < 0")]
        [Throws(typeof(ArgumentException), "Pal.Contents(array).Length - arrayIndex < @this.SpecCount")]
        [Ensures("0 <= arrayIndex && arrayIndex + @this.SpecCount <= Pal.Contents(array).Length")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("Pal.Forall((int j) => Pal.Implies(0 <= j && j < @this.SpecCount, j < @this.SpecKeys.Length && j < @this.SpecValues.Length && Pal.Same(Pal.Contents(array)[arrayIndex + j].Key, @this.SpecKeys[j]) && Pal.Same(Pal.Contents(array)[arrayIndex + j].Value, @this.SpecValues[j])))")]
        [Ensures("Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Contents(array).Length && (j < arrayIndex || j >= arrayIndex + @this.SpecCount), Pal.Same(Pal.Contents(array)[j], Pal.Old(Pal.Contents(array))[j])))")]
        void ICollection<KeyValuePair<TKey, TValue>>.CopyTo(KeyValuePair<TKey, TValue>[] array, int arrayIndex)
        {
            ArgumentNullException.ThrowIfNull(array);
            ThrowIfNegative(arrayIndex);
            if (array.Length - arrayIndex < _count)
            {
                throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall);
            }

            Ghost<int> start = arrayIndex;
            for (int i = 0; i < _count; i++)
            {
                Pal.Invariant(0 <= i && i <= _count && arrayIndex == start.Value + i);
                Pal.Invariant(Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length);
                Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < i, Pal.Same(Pal.Contents(array)[start.Value + j].Key, Pal.Contents(_entries)[j].Key) && Pal.Same(Pal.Contents(array)[start.Value + j].Value, Pal.Contents(_entries)[j].Value))));
                Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Contents(array).Length && (j < start.Value || j >= start.Value + _count), Pal.Same(Pal.Contents(array)[j], Pal.Old(Pal.Contents(array))[j]))));
                ref Entry entry = ref _entries![i];
                array[arrayIndex++] = new(entry.Key, entry.Value);
            }
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(item.Key)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(Result, @this.SpecCount == Pal.Old(@this.SpecCount) - 1 && Pal.Exists((int i) => 0 <= i && i < Pal.Old(@this.SpecCount) && i < Pal.Old(@this.SpecKeys).Length && i < Pal.Old(@this.SpecValues).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, Pal.Old(@this.SpecKeys)[i], item.Key) && Pal.DefaultEquals(Pal.Old(@this.SpecValues)[i], item.Value) && @this.SpecKeys == OrderedDictionary<TKey, TValue>.DelK(Pal.Old(@this.SpecKeys), i) && @this.SpecValues == OrderedDictionary<TKey, TValue>.DelV(Pal.Old(@this.SpecValues), i)))")]
        [Ensures("Pal.Implies(!Result, @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues))")]
        [Ensures("Pal.Implies(!Result, !Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, item.Key)) || Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], item.Key) && !Pal.DefaultEquals(@this.SpecValues[i], item.Value)))")]
        bool ICollection<KeyValuePair<TKey, TValue>>.Remove(KeyValuePair<TKey, TValue> item)
        {
            if (TryGetValue(item.Key, out TValue? value, out int index) && EqualityComparer<TValue>.Default.Equals(value, item.Value))
            {
                RemoveAt(index);
                return true;
            }

            return false;
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key) || (Pal.IsNull(value) && !Pal.IsNull(default(TValue)))")]
        [Throws(typeof(ArgumentException), "!Pal.IsA<TKey>(key) || (!Pal.IsNull(value) && !Pal.IsA<TValue>(value)) || OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<TKey>(key)) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("Pal.IsA<TKey>(key) && (Pal.IsNull(value) || Pal.IsA<TValue>(value)) && !Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<TKey>(key))) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), Pal.Old(@this.SpecCount), Pal.Unbox<TKey>(key)) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), Pal.Old(@this.SpecCount), (Pal.IsA<TValue>(value) ? Pal.Unbox<TValue>(value) : default(TValue)))")]
        void IDictionary.Add(object key, object? value)
        {
            ArgumentNullException.ThrowIfNull(key);
            if (default(TValue) is not null)
            {
                ArgumentNullException.ThrowIfNull(value);
            }

            if (key is not TKey tkey)
            {
                throw new ArgumentException(SR.Format(SR.Arg_WrongType, key, typeof(TKey)), nameof(key));
            }

            TValue tvalue = default!;
            if (value is not null)
            {
                if (value is not TValue temp)
                {
                    throw new ArgumentException(SR.Format(SR.Arg_WrongType, value, typeof(TValue)), nameof(value));
                }

                tvalue = temp;
            }

            Add(tkey, tvalue);
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Ensures("Result == (Pal.IsA<TKey>(key) && OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<TKey>(key)))")]
        bool IDictionary.Contains(object key)
        {
            ArgumentNullException.ThrowIfNull(key);

            return key is TKey tkey && ContainsKey(tkey);
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(!(Pal.IsA<TKey>(key) && OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, Pal.Old(@this.SpecKeys), Pal.Unbox<TKey>(key))), @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues))")]
        [Ensures("Pal.Implies(Pal.IsA<TKey>(key) && OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, Pal.Old(@this.SpecKeys), Pal.Unbox<TKey>(key)), @this.SpecCount == Pal.Old(@this.SpecCount) - 1 && Pal.Exists((int i) => 0 <= i && i < Pal.Old(@this.SpecCount) && i < Pal.Old(@this.SpecKeys).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, Pal.Old(@this.SpecKeys)[i], Pal.Unbox<TKey>(key)) && @this.SpecKeys == OrderedDictionary<TKey, TValue>.DelK(Pal.Old(@this.SpecKeys), i) && @this.SpecValues == OrderedDictionary<TKey, TValue>.DelV(Pal.Old(@this.SpecValues), i)))")]
        void IDictionary.Remove(object key)
        {
            ArgumentNullException.ThrowIfNull(key);

            if (key is TKey tkey)
            {
                Remove(tkey);
            }
        }

        /// <inheritdoc/>
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

            ThrowIfNegative(index);

            if (array.Length - index < _count)
            {
                throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall);
            }

            if (array is KeyValuePair<TKey, TValue>[] tarray)
            {
                ((ICollection<KeyValuePair<TKey, TValue>>)this).CopyTo(tarray, index);
            }
            else
            {
                try
                {
                    if (array is not object[] objects)
                    {
                        throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                    }

                    foreach (KeyValuePair<TKey, TValue> pair in this)
                    {
                        objects[index++] = pair;
                    }
                }
                catch (ArrayTypeMismatchException)
                {
                    throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                }
            }
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsA<KeyValuePair<TKey, TValue>>(value) && Pal.IsNull(Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key)")]
        [Throws(typeof(ArgumentException), "!Pal.IsA<KeyValuePair<TKey, TValue>>(value) || OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("Pal.IsA<KeyValuePair<TKey, TValue>>(value) && !Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer) && Result == Pal.Old(@this.SpecCount)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), Pal.Old(@this.SpecCount), Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), Pal.Old(@this.SpecCount), Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value)")]
        int IList.Add(object? value)
        {
            if (value is not KeyValuePair<TKey, TValue> pair)
            {
                throw new ArgumentException(SR.Format(SR.Arg_WrongType, value, typeof(KeyValuePair<TKey, TValue>)), nameof(value));
            }

            Add(pair.Key, pair.Value);
            return Count - 1;
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsA<KeyValuePair<TKey, TValue>>(value) && Pal.IsNull(Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key)")]
        [Ensures("Pal.Implies(Result, Pal.IsA<KeyValuePair<TKey, TValue>>(value) && Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) && Pal.DefaultEquals(@this.SpecValues[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value)))")]
        [Ensures("Pal.Implies(!Result, !Pal.IsA<KeyValuePair<TKey, TValue>>(value) || !OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) || Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) && !Pal.DefaultEquals(@this.SpecValues[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value)))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        bool IList.Contains(object? value) =>
            value is KeyValuePair<TKey, TValue> pair &&
            TryGetValue(pair.Key, out TValue? v) &&
            EqualityComparer<TValue>.Default.Equals(v, pair.Value);

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsA<KeyValuePair<TKey, TValue>>(value) && Pal.IsNull(Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key)")]
        [Ensures("-1 <= Result")]
        [Ensures("Pal.Implies(Result >= 0, Result < @this.SpecCount && Pal.IsA<KeyValuePair<TKey, TValue>>(value) && Result < @this.SpecKeys.Length && Result < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[Result], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) && Pal.DefaultEquals(Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value, @this.SpecValues[Result]))")]
        [Ensures("Pal.Implies(Result < 0, !Pal.IsA<KeyValuePair<TKey, TValue>>(value) || !OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) || Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) && !Pal.DefaultEquals(Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value, @this.SpecValues[i])))")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        int IList.IndexOf(object? value)
        {
            if (value is KeyValuePair<TKey, TValue> pair)
            {
                return ((IList<KeyValuePair<TKey, TValue>>)this).IndexOf(pair);
            }

            return -1;
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index > @this.SpecCount")]
        [Throws(typeof(ArgumentNullException), "Pal.IsA<KeyValuePair<TKey, TValue>>(value) && Pal.IsNull(Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key)")]
        [Throws(typeof(ArgumentException), "!Pal.IsA<KeyValuePair<TKey, TValue>>(value) || OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) || @this.SpecCapacity >= System.Collections.HashHelpers.MaxPrimeArrayLength")]
        [Ensures("Pal.IsA<KeyValuePair<TKey, TValue>>(value) && 0 <= index && index <= Pal.Old(@this.SpecCount) && !Pal.Old(OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key)) && @this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1 && @this.SpecKeys == OrderedDictionary<TKey, TValue>.InsK(Pal.Old(@this.SpecKeys), index, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) && @this.SpecValues == OrderedDictionary<TKey, TValue>.InsV(Pal.Old(@this.SpecValues), index, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value)")]
        void IList.Insert(int index, object? value)
        {
            if (value is not KeyValuePair<TKey, TValue> pair)
            {
                throw new ArgumentException(SR.Format(SR.Arg_WrongType, value, typeof(KeyValuePair<TKey, TValue>)), nameof(value));
            }

            Insert(index, pair.Key, pair.Value);
        }

        /// <inheritdoc/>
        [Throws(typeof(ArgumentNullException), "Pal.IsA<KeyValuePair<TKey, TValue>>(value) && Pal.IsNull(Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(!Pal.IsA<KeyValuePair<TKey, TValue>>(value), @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues))")]
        [Ensures("Pal.Implies(Pal.IsA<KeyValuePair<TKey, TValue>>(value) && @this.SpecCount != Pal.Old(@this.SpecCount), @this.SpecCount == Pal.Old(@this.SpecCount) - 1 && Pal.Exists((int i) => 0 <= i && i < Pal.Old(@this.SpecCount) && i < Pal.Old(@this.SpecKeys).Length && i < Pal.Old(@this.SpecValues).Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, Pal.Old(@this.SpecKeys)[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) && Pal.DefaultEquals(Pal.Old(@this.SpecValues)[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value) && @this.SpecKeys == OrderedDictionary<TKey, TValue>.DelK(Pal.Old(@this.SpecKeys), i) && @this.SpecValues == OrderedDictionary<TKey, TValue>.DelV(Pal.Old(@this.SpecValues), i)))")]
        [Ensures("Pal.Implies(Pal.IsA<KeyValuePair<TKey, TValue>>(value) && @this.SpecCount == Pal.Old(@this.SpecCount), @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && (!OrderedDictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) || Pal.Exists((int i) => 0 <= i && i < @this.SpecCount && i < @this.SpecKeys.Length && i < @this.SpecValues.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this.SpecComparer, @this.SpecKeys[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Key) && !Pal.DefaultEquals(@this.SpecValues[i], Pal.Unbox<KeyValuePair<TKey, TValue>>(value).Value))))")]
        void IList.Remove(object? value)
        {
            if (value is KeyValuePair<TKey, TValue> pair)
            {
                ((ICollection<KeyValuePair<TKey, TValue>>)this).Remove(pair);
            }
        }

        /// <summary>Represents a key/value pair in the dictionary.</summary>
        private struct Entry
        {
            /// <summary>The index of the next entry in the chain, or -1 if this is the last entry in the chain.</summary>
            public int Next;
            /// <summary>Cached hash code of <see cref="Key"/>.</summary>
            public uint HashCode;
            /// <summary>The key.</summary>
            public TKey Key;
            /// <summary>The value associated with <see cref="Key"/>.</summary>
            public TValue Value;
        }

        /// <summary>Enumerates the elements of a <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        [StructLayout(LayoutKind.Auto)]
        public struct Enumerator : IEnumerator<KeyValuePair<TKey, TValue>>, IDictionaryEnumerator
        {
            /// <summary>The dictionary being enumerated.</summary>
            private readonly OrderedDictionary<TKey, TValue> _dictionary;
            /// <summary>A snapshot of the dictionary's version when enumeration began.</summary>
            private readonly int _version;
            /// <summary>Whether Current should be a DictionaryEntry.</summary>
            private readonly bool _useDictionaryEntry;
            /// <summary>The current index.</summary>
            private int _index;

            // R32.12. What the key and value enumerators, which wrap this one, state of it.
            [Spec] internal bool SpecFresh => _version == _dictionary.SpecVersion;
            [Spec] internal SpecInt SpecIndex => _index;
            [Spec] internal SpecInt SpecCount => _dictionary.SpecCount;
            [Spec] internal Seq<TKey> SpecKeys => _dictionary.SpecKeys;
            [Spec] internal Seq<TValue> SpecValues => _dictionary.SpecValues;
            [Spec] internal KeyValuePair<TKey, TValue> SpecCurrent => Current;

            /// <summary>Initialize the enumerator.</summary>
            [Ensures("ReferenceEquals(@this._dictionary, dictionary) && @this._version == dictionary.SpecVersion && @this._index == 0")]
            [Ensures("@this._useDictionaryEntry == useDictionaryEntry")]
            internal Enumerator(OrderedDictionary<TKey, TValue> dictionary, bool useDictionaryEntry)
            {
                _dictionary = dictionary;
                _version = _dictionary._version;
                _useDictionaryEntry = useDictionaryEntry;
            }

            /// <inheritdoc/>
            public KeyValuePair<TKey, TValue> Current { get; private set; }

            /// <inheritdoc/>
            [Ensures("Pal.Implies(@this._useDictionaryEntry, Pal.Boxes(Result, new System.Collections.DictionaryEntry(@this.Current.Key, @this.Current.Value)))")]
            [Ensures("Pal.Implies(!@this._useDictionaryEntry, Pal.Boxes(Result, @this.Current))")]
            readonly object IEnumerator.Current => _useDictionaryEntry ?
                new DictionaryEntry(Current.Key, Current.Value) :
                Current;

            /// <inheritdoc/>
            [Ensures("Pal.Boxes(Result.Key, @this.Current.Key) && Pal.Boxes(Result.Value, @this.Current.Value)")]
            readonly DictionaryEntry IDictionaryEnumerator.Entry => new(Current.Key, Current.Value);

            /// <inheritdoc/>
            [Ensures("Pal.Boxes(Result, @this.Current.Key)")]
            readonly object IDictionaryEnumerator.Key => Current.Key;

            /// <inheritdoc/>
            [Ensures("Pal.Boxes(Result, @this.Current.Value)")]
            readonly object? IDictionaryEnumerator.Value => Current.Value;

            /// <inheritdoc/>
            [Requires("0 <= @this._index")]
            [Throws(typeof(InvalidOperationException), "@this._version != @this._dictionary.SpecVersion")]
            [Ensures("@this._version == @this._dictionary.SpecVersion && 0 <= @this._index")]
            [Ensures("Result == (Pal.Old(@this._index) < @this._dictionary.SpecCount)")]
            [Ensures("Pal.Implies(Result, @this._index == Pal.Old(@this._index) + 1 && Pal.Old(@this._index) < @this._dictionary.SpecKeys.Length && Pal.Old(@this._index) < @this._dictionary.SpecValues.Length && Pal.Same(@this.Current.Key, @this._dictionary.SpecKeys[Pal.Old(@this._index)]) && Pal.Same(@this.Current.Value, @this._dictionary.SpecValues[Pal.Old(@this._index)]))")]
            [Ensures("Pal.Implies(!Result, @this._index == Pal.Old(@this._index))")]
            public bool MoveNext()
            {
                OrderedDictionary<TKey, TValue> dictionary = _dictionary;

                if (_version != dictionary._version)
                {
                    ThrowHelper.ThrowVersionCheckFailed();
                }

                if (_index < dictionary._count)
                {
                    Debug.Assert(dictionary._entries is not null);
                    ref Entry entry = ref dictionary._entries[_index];
                    Current = new KeyValuePair<TKey, TValue>(entry.Key, entry.Value);
                    _index++;
                    return true;
                }

                Current = default;
                return false;
            }

            /// <inheritdoc/>
            [Throws(typeof(InvalidOperationException), "@this._version != @this._dictionary.SpecVersion")]
            [Ensures("@this._version == @this._dictionary.SpecVersion && @this._index == 0")]
            void IEnumerator.Reset()
            {
                if (_version != _dictionary._version)
                {
                    ThrowHelper.ThrowVersionCheckFailed();
                }

                _index = 0;
                Current = default;
            }

            /// <inheritdoc/>
            [Ensures("true")]
            readonly void IDisposable.Dispose() { }
        }

        /// <summary>Represents the collection of keys in a <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        [DebuggerTypeProxy(typeof(ICollectionDebugView<>))]
        [DebuggerDisplay("Count = {Count}")]
        public sealed class KeyCollection : IList<TKey>, IReadOnlyList<TKey>, IList
        {
            /// <summary>The dictionary whose keys are being exposed.</summary>
            private readonly OrderedDictionary<TKey, TValue> _dictionary;

            /// <summary>Initialize the collection wrapper.</summary>
            [Ensures("ReferenceEquals(@this._dictionary, dictionary)")]
            internal KeyCollection(OrderedDictionary<TKey, TValue> dictionary) => _dictionary = dictionary;

            /// <inheritdoc/>
            [Ensures("Result == @this._dictionary.SpecCount")]
            public int Count => _dictionary.Count;

            /// <inheritdoc/>
            [Ensures("Result")]
            bool ICollection<TKey>.IsReadOnly => true;

            /// <inheritdoc/>
            [Ensures("Result")]
            bool IList.IsReadOnly => true;

            /// <inheritdoc/>
            [Ensures("!Result")]
            bool IList.IsFixedSize => false;

            /// <inheritdoc/>
            [Ensures("!Result")]
            bool ICollection.IsSynchronized => false;

            /// <inheritdoc/>
            object ICollection.SyncRoot => ((ICollection)_dictionary).SyncRoot;

            /// <inheritdoc/>
            [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
            [Ensures("Result == OrderedDictionary<TKey, TValue>.Mem(@this._dictionary.SpecComparer, @this._dictionary.SpecKeys, key)")]
            public bool Contains(TKey key) => _dictionary.ContainsKey(key);

            /// <inheritdoc/>
            [Ensures("Result == (Pal.IsA<TKey>(value) && OrderedDictionary<TKey, TValue>.Mem(@this._dictionary.SpecComparer, @this._dictionary.SpecKeys, Pal.Unbox<TKey>(value)))")]
            bool IList.Contains(object? value) => value is TKey key && Contains(key);

            /// <inheritdoc/>
            [Throws(typeof(ArgumentOutOfRangeException), "arrayIndex < 0")]
            [Throws(typeof(ArgumentException), "Pal.Contents(array).Length - arrayIndex < @this._dictionary.SpecCount")]
            [Ensures("0 <= arrayIndex && arrayIndex + @this._dictionary.SpecCount <= Pal.Contents(array).Length")]
            [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
            [Ensures("Pal.Forall((int j) => Pal.Implies(0 <= j && j < @this._dictionary.SpecCount, j < @this._dictionary.SpecKeys.Length && Pal.Same(Pal.Contents(array)[arrayIndex + j], @this._dictionary.SpecKeys[j])))")]
            [Ensures("Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Contents(array).Length && (j < arrayIndex || j >= arrayIndex + @this._dictionary.SpecCount), Pal.Same(Pal.Contents(array)[j], Pal.Old(Pal.Contents(array))[j])))")]
            public void CopyTo(TKey[] array, int arrayIndex)
            {
                ArgumentNullException.ThrowIfNull(array);
                ThrowIfNegative(arrayIndex);

                OrderedDictionary<TKey, TValue> dictionary = _dictionary;
                int count = dictionary._count;

                if (array.Length - arrayIndex < count)
                {
                    throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall, nameof(array));
                }

                Entry[]? entries = dictionary._entries;
                Ghost<int> start = arrayIndex;
                for (int i = 0; i < count; i++)
                {
                    Pal.Invariant(0 <= i && i <= count && arrayIndex == start.Value + i);
                    Pal.Invariant(Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length);
                    Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < i, Pal.Same(Pal.Contents(array)[start.Value + j], Pal.Contents(entries!)[j].Key))));
                    Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Contents(array).Length && (j < start.Value || j >= start.Value + count), Pal.Same(Pal.Contents(array)[j], Pal.Old(Pal.Contents(array))[j]))));
                    Debug.Assert(entries is not null);
                    array[arrayIndex++] = entries[i].Key;
                }
            }

            /// <inheritdoc/>
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

                ThrowIfNegative(index);

                if (array.Length - index < _dictionary.Count)
                {
                    throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall);
                }

                if (array is TKey[] keys)
                {
                    CopyTo(keys, index);
                }
                else
                {
                    try
                    {
                        if (array is not object?[] objects)
                        {
                            throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                        }

                        foreach (TKey key in this)
                        {
                            objects[index++] = key;
                        }
                    }
                    catch (ArrayTypeMismatchException)
                    {
                        throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                    }
                }
            }

            /// <inheritdoc/>
            TKey IList<TKey>.this[int index]
            {
                [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this._dictionary.SpecCount")]
                [Ensures("0 <= index && index < @this._dictionary.SpecCount && index < @this._dictionary.SpecKeys.Length && Pal.Same(Result, @this._dictionary.SpecKeys[index])")]
                get => _dictionary.GetAt(index).Key;
                [Throws(typeof(NotSupportedException))]
                [Ensures("false")]
                set => throw new NotSupportedException();
            }

            /// <inheritdoc/>
            object? IList.this[int index]
            {
                [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this._dictionary.SpecCount")]
                [Ensures("0 <= index && index < @this._dictionary.SpecCount && index < @this._dictionary.SpecKeys.Length && Pal.Boxes(Result, @this._dictionary.SpecKeys[index])")]
                get => _dictionary.GetAt(index).Key;
                [Throws(typeof(NotSupportedException))]
                [Ensures("false")]
                set => throw new NotSupportedException();
            }

            /// <inheritdoc/>
            [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this._dictionary.SpecCount")]
            [Ensures("0 <= index && index < @this._dictionary.SpecCount && index < @this._dictionary.SpecKeys.Length && Pal.Same(Result, @this._dictionary.SpecKeys[index])")]
            TKey IReadOnlyList<TKey>.this[int index] => _dictionary.GetAt(index).Key;

            /// <summary>Returns an enumerator that iterates through the <see cref="OrderedDictionary{TKey, TValue}.KeyCollection"/>.</summary>
            /// <returns>A <see cref="OrderedDictionary{TKey, TValue}.KeyCollection.Enumerator"/> for the <see cref="OrderedDictionary{TKey, TValue}.KeyCollection"/>.</returns>
            [Ensures("ReferenceEquals(Result._enumerator._dictionary, @this._dictionary) && Result._enumerator._version == @this._dictionary.SpecVersion && Result._enumerator._index == 0")]
            public Enumerator GetEnumerator() => new(_dictionary);

            /// <inheritdoc/>
            [Ensures("Pal.Implies(@this._dictionary.SpecCount != 0, Pal.Exists((OrderedDictionary<TKey, TValue>.KeyCollection.Enumerator e) => Pal.Boxes(Result, e) && " +
                "ReferenceEquals(e._enumerator._dictionary, @this._dictionary) && e._enumerator._version == @this._dictionary.SpecVersion && e._enumerator._index == 0))")]
            IEnumerator<TKey> IEnumerable<TKey>.GetEnumerator() =>
                Count == 0 ? EnumerableHelpers.GetEmptyEnumerator<TKey>() :
                GetEnumerator();

            /// <inheritdoc/>
            IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<TKey>)this).GetEnumerator();

            /// <inheritdoc/>
            [Throws(typeof(ArgumentNullException), "Pal.IsNull(item)")]
            [Ensures("-1 <= Result && Result < @this._dictionary.SpecCount")]
            [Ensures("Implies(Result >= 0, Result < @this._dictionary.SpecKeys.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this._dictionary.SpecComparer, @this._dictionary.SpecKeys[Result], item))")]
            [Ensures("(Result >= 0) == OrderedDictionary<TKey, TValue>.Mem(@this._dictionary.SpecComparer, @this._dictionary.SpecKeys, item)")]
            int IList<TKey>.IndexOf(TKey item) => _dictionary.IndexOf(item);

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void ICollection<TKey>.Add(TKey item) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void ICollection<TKey>.Clear() => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList<TKey>.Insert(int index, TKey item) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            bool ICollection<TKey>.Remove(TKey item) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList<TKey>.RemoveAt(int index) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            int IList.Add(object? value) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList.Clear() => throw new NotSupportedException();

            /// <inheritdoc/>
            [Ensures("-1 <= Result && Pal.Implies(Result >= 0, Result < @this._dictionary.SpecCount)")]
            [Ensures("(Result >= 0) == (Pal.IsA<TKey>(value) && OrderedDictionary<TKey, TValue>.Mem(@this._dictionary.SpecComparer, @this._dictionary.SpecKeys, Pal.Unbox<TKey>(value)))")]
            [Ensures("Pal.Implies(Result >= 0, Pal.IsA<TKey>(value) && Result < @this._dictionary.SpecKeys.Length && OrderedDictionary<TKey, TValue>.KeyEq(@this._dictionary.SpecComparer, @this._dictionary.SpecKeys[Result], Pal.Unbox<TKey>(value)))")]
            int IList.IndexOf(object? value) => value is TKey key ? _dictionary.IndexOf(key) : -1;

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList.Insert(int index, object? value) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList.Remove(object? value) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList.RemoveAt(int index) => throw new NotSupportedException();

            /// <summary>Enumerates the elements of a <see cref="OrderedDictionary{TKey, TValue}.KeyCollection"/>.</summary>
            public struct Enumerator : IEnumerator<TKey>
            {
                /// <summary>The dictionary's enumerator.</summary>
                private OrderedDictionary<TKey, TValue>.Enumerator _enumerator;

                /// <summary>Initialize the enumerator.</summary>
                [Ensures("@this._enumerator.SpecFresh && @this._enumerator.SpecIndex == 0")]
                internal Enumerator(OrderedDictionary<TKey, TValue> dictionary) => _enumerator = dictionary.GetEnumerator();

                /// <inheritdoc/>
                [Ensures("Pal.Same(Result, @this._enumerator.SpecCurrent.Key)")]
                public TKey Current => _enumerator.Current.Key;

                /// <inheritdoc/>
                [Ensures("Pal.Boxes(Result, @this._enumerator.SpecCurrent.Key)")]
                object IEnumerator.Current => Current;

                /// <inheritdoc/>
                [Requires("0 <= @this._enumerator.SpecIndex")]
                [Throws(typeof(InvalidOperationException), "!@this._enumerator.SpecFresh")]
                [Ensures("@this._enumerator.SpecFresh && 0 <= @this._enumerator.SpecIndex")]
                [Ensures("Result == (Pal.Old(@this._enumerator.SpecIndex) < @this._enumerator.SpecCount)")]
                [Ensures("Pal.Implies(Result, @this._enumerator.SpecIndex == Pal.Old(@this._enumerator.SpecIndex) + 1 && Pal.Old(@this._enumerator.SpecIndex) < @this._enumerator.SpecKeys.Length && Pal.Same(@this._enumerator.SpecCurrent.Key, @this._enumerator.SpecKeys[Pal.Old(@this._enumerator.SpecIndex)]))")]
                [Ensures("Pal.Implies(!Result, @this._enumerator.SpecIndex == Pal.Old(@this._enumerator.SpecIndex))")]
                public bool MoveNext() => _enumerator.MoveNext();

                /// <inheritdoc/>
                [Throws(typeof(InvalidOperationException), "!@this._enumerator.SpecFresh")]
                [Ensures("@this._enumerator.SpecFresh && @this._enumerator.SpecIndex == 0")]
                void IEnumerator.Reset() => EnumerableHelpers.Reset(ref _enumerator);

                /// <inheritdoc/>
                [Ensures("true")]
                readonly void IDisposable.Dispose() { }
            }
        }

        /// <summary>Represents the collection of values in a <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
        [DebuggerTypeProxy(typeof(ICollectionDebugView<>))]
        [DebuggerDisplay("Count = {Count}")]
        public sealed class ValueCollection : IList<TValue>, IReadOnlyList<TValue>, IList
        {
            /// <summary>The dictionary whose values are being exposed.</summary>
            private readonly OrderedDictionary<TKey, TValue> _dictionary;

            /// <summary>Initialize the collection wrapper.</summary>
            [Ensures("ReferenceEquals(@this._dictionary, dictionary)")]
            internal ValueCollection(OrderedDictionary<TKey, TValue> dictionary) => _dictionary = dictionary;

            /// <inheritdoc/>
            [Ensures("Result == @this._dictionary.SpecCount")]
            public int Count => _dictionary.Count;

            /// <inheritdoc/>
            [Ensures("Result")]
            bool ICollection<TValue>.IsReadOnly => true;

            /// <inheritdoc/>
            [Ensures("Result")]
            bool IList.IsReadOnly => true;

            /// <inheritdoc/>
            [Ensures("!Result")]
            bool IList.IsFixedSize => false;

            /// <inheritdoc/>
            [Ensures("!Result")]
            bool ICollection.IsSynchronized => false;

            /// <inheritdoc/>
            object ICollection.SyncRoot => ((ICollection)_dictionary).SyncRoot;

            /// <inheritdoc/>
            [Throws(typeof(ArgumentOutOfRangeException), "arrayIndex < 0")]
            [Throws(typeof(ArgumentException), "Pal.Contents(array).Length - arrayIndex < @this._dictionary.SpecCount")]
            [Ensures("0 <= arrayIndex && arrayIndex + @this._dictionary.SpecCount <= Pal.Contents(array).Length")]
            [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
            [Ensures("Pal.Forall((int j) => Pal.Implies(0 <= j && j < @this._dictionary.SpecCount, j < @this._dictionary.SpecValues.Length && Pal.Same(Pal.Contents(array)[arrayIndex + j], @this._dictionary.SpecValues[j])))")]
            [Ensures("Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Contents(array).Length && (j < arrayIndex || j >= arrayIndex + @this._dictionary.SpecCount), Pal.Same(Pal.Contents(array)[j], Pal.Old(Pal.Contents(array))[j])))")]
            public void CopyTo(TValue[] array, int arrayIndex)
            {
                ArgumentNullException.ThrowIfNull(array);
                ThrowIfNegative(arrayIndex);

                OrderedDictionary<TKey, TValue> dictionary = _dictionary;
                int count = dictionary._count;

                if (array.Length - arrayIndex < count)
                {
                    throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall, nameof(array));
                }

                Entry[]? entries = dictionary._entries;
                Ghost<int> start = arrayIndex;
                for (int i = 0; i < count; i++)
                {
                    Pal.Invariant(0 <= i && i <= count && arrayIndex == start.Value + i);
                    Pal.Invariant(Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length);
                    Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < i, Pal.Same(Pal.Contents(array)[start.Value + j], Pal.Contents(entries!)[j].Value))));
                    Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Contents(array).Length && (j < start.Value || j >= start.Value + count), Pal.Same(Pal.Contents(array)[j], Pal.Old(Pal.Contents(array))[j]))));
                    Debug.Assert(entries is not null);
                    array[arrayIndex++] = entries[i].Value;
                }
            }

            /// <summary>Returns an enumerator that iterates through the <see cref="OrderedDictionary{TKey, TValue}.ValueCollection"/>.</summary>
            /// <returns>A <see cref="OrderedDictionary{TKey, TValue}.ValueCollection.Enumerator"/> for the <see cref="OrderedDictionary{TKey, TValue}.ValueCollection"/>.</returns>
            [Ensures("ReferenceEquals(Result._enumerator._dictionary, @this._dictionary) && Result._enumerator._version == @this._dictionary.SpecVersion && Result._enumerator._index == 0")]
            public Enumerator GetEnumerator() => new(_dictionary);

            /// <inheritdoc/>
            TValue IList<TValue>.this[int index]
            {
                [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this._dictionary.SpecCount")]
                [Ensures("0 <= index && index < @this._dictionary.SpecCount && index < @this._dictionary.SpecValues.Length && Pal.Same(Result, @this._dictionary.SpecValues[index])")]
                get => _dictionary.GetAt(index).Value;
                [Throws(typeof(NotSupportedException))]
                [Ensures("false")]
                set => throw new NotSupportedException();
            }

            /// <inheritdoc/>
            [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this._dictionary.SpecCount")]
            [Ensures("0 <= index && index < @this._dictionary.SpecCount && index < @this._dictionary.SpecValues.Length && Pal.Same(Result, @this._dictionary.SpecValues[index])")]
            TValue IReadOnlyList<TValue>.this[int index] => _dictionary.GetAt(index).Value;

            /// <inheritdoc/>
            object? IList.this[int index]
            {
                [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this._dictionary.SpecCount")]
                [Ensures("0 <= index && index < @this._dictionary.SpecCount && index < @this._dictionary.SpecValues.Length && Pal.Boxes(Result, @this._dictionary.SpecValues[index])")]
                get => _dictionary.GetAt(index).Value;
                [Throws(typeof(NotSupportedException))]
                [Ensures("false")]
                set => throw new NotSupportedException();
            }

            /// <inheritdoc/>
            [Ensures("Result == OrderedDictionary<TKey, TValue>.HasValue(@this._dictionary.SpecValues, item, @this._dictionary.SpecCount)")]
            bool ICollection<TValue>.Contains(TValue item) => _dictionary.ContainsValue(item);

            /// <inheritdoc/>
            [Ensures("Pal.Implies(@this._dictionary.SpecCount != 0, Pal.Exists((OrderedDictionary<TKey, TValue>.ValueCollection.Enumerator e) => Pal.Boxes(Result, e) && " +
                "ReferenceEquals(e._enumerator._dictionary, @this._dictionary) && e._enumerator._version == @this._dictionary.SpecVersion && e._enumerator._index == 0))")]
            IEnumerator<TValue> IEnumerable<TValue>.GetEnumerator() =>
                Count == 0 ? EnumerableHelpers.GetEmptyEnumerator<TValue>() :
                GetEnumerator();

            /// <inheritdoc/>
            IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<TValue>)this).GetEnumerator();

            /// <inheritdoc/>
            [Ensures("-1 <= Result && Result < @this._dictionary.SpecCount")]
            [Ensures("Pal.Implies(0 <= Result, Result < @this._dictionary.SpecValues.Length && Pal.DefaultEquals(item, @this._dictionary.SpecValues[Result]) && !OrderedDictionary<TKey, TValue>.HasValue(@this._dictionary.SpecValues, item, Result))")]
            [Ensures("Pal.Implies(Result < 0, !OrderedDictionary<TKey, TValue>.HasValue(@this._dictionary.SpecValues, item, @this._dictionary.SpecCount))")]
            int IList<TValue>.IndexOf(TValue item)
            {
                Entry[]? entries = _dictionary._entries;
                if (entries is not null)
                {
                    int count = _dictionary._count;
                    for (int i = 0; i < count; i++)
                    {
                        Pal.Invariant(0 <= i && i <= count);
                        Pal.Invariant(!HasValue(ValuesOf(Pal.Contents(entries), count), item, i));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), 0 <= Pal.Result<int>() && Pal.Result<int>() < count && Pal.Result<int>() < ValuesOf(Pal.Contents(entries), count).Length &&
                            Pal.DefaultEquals(item, ValuesOf(Pal.Contents(entries), count)[Pal.Result<int>()]) && !HasValue(ValuesOf(Pal.Contents(entries), count), item, Pal.Result<int>())));
                        if (EqualityComparer<TValue>.Default.Equals(item, entries[i].Value))
                        {
                            return i;
                        }
                    }
                }

                return -1;
            }

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void ICollection<TValue>.Add(TValue item) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void ICollection<TValue>.Clear() => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList<TValue>.Insert(int index, TValue item) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            bool ICollection<TValue>.Remove(TValue item) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList<TValue>.RemoveAt(int index) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            int IList.Add(object? value) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList.Clear() => throw new NotSupportedException();

            /// <inheritdoc/>
            [Ensures("Result == (Pal.IsNull(value) && Pal.IsNull(default(TValue)) ? OrderedDictionary<TKey, TValue>.HasValue(@this._dictionary.SpecValues, default(TValue), @this._dictionary.SpecCount) : Pal.IsA<TValue>(value) && OrderedDictionary<TKey, TValue>.HasValue(@this._dictionary.SpecValues, Pal.Unbox<TValue>(value), @this._dictionary.SpecCount))")]
            bool IList.Contains(object? value) =>
                value is null && default(TValue) is null ?
                    _dictionary.ContainsValue(default!) :
                    value is TValue tvalue && _dictionary.ContainsValue(tvalue);

            /// <inheritdoc/>
            [Ensures("-1 <= Result && Pal.Implies(0 <= Result, Result < @this._dictionary.SpecCount && Result < @this._dictionary.SpecValues.Length)")]
            [Ensures("Pal.Implies(0 <= Result && Pal.IsNull(value), Pal.IsNull(@this._dictionary.SpecValues[Result]))")]
            [Ensures("Pal.Implies(0 <= Result && !Pal.IsNull(value), Pal.IsA<TValue>(value) && Pal.DefaultEquals(Pal.Unbox<TValue>(value), @this._dictionary.SpecValues[Result]) && !OrderedDictionary<TKey, TValue>.HasValue(@this._dictionary.SpecValues, Pal.Unbox<TValue>(value), Result))")]
            [Ensures("Pal.Implies(Result < 0 && Pal.IsA<TValue>(value), !OrderedDictionary<TKey, TValue>.HasValue(@this._dictionary.SpecValues, Pal.Unbox<TValue>(value), @this._dictionary.SpecCount))")]
            int IList.IndexOf(object? value)
            {
                Entry[]? entries = _dictionary._entries;
                if (entries is not null)
                {
                    int count = _dictionary._count;

                    if (value is null && default(TValue) is null)
                    {
                        for (int i = 0; i < count; i++)
                        {
                            Pal.Invariant(0 <= i && i <= count);
                            Pal.Invariant(Pal.Implies(Pal.Returned(), 0 <= Pal.Result<int>() && Pal.Result<int>() < count && Pal.Result<int>() < ValuesOf(Pal.Contents(entries), count).Length && Pal.IsNull(ValuesOf(Pal.Contents(entries), count)[Pal.Result<int>()])));
                            if (entries[i].Value is null)
                            {
                                return i;
                            }
                        }
                    }
                    else if (value is TValue tvalue)
                    {
                        for (int i = 0; i < count; i++)
                        {
                            Pal.Invariant(0 <= i && i <= count);
                            Pal.Invariant(Pal.IsA<TValue>(value) && !HasValue(ValuesOf(Pal.Contents(entries), count), Pal.Unbox<TValue>(value), i));
                            Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.IsA<TValue>(value) && 0 <= Pal.Result<int>() && Pal.Result<int>() < count && Pal.Result<int>() < ValuesOf(Pal.Contents(entries), count).Length &&
                                Pal.DefaultEquals(Pal.Unbox<TValue>(value), ValuesOf(Pal.Contents(entries), count)[Pal.Result<int>()]) && !HasValue(ValuesOf(Pal.Contents(entries), count), Pal.Unbox<TValue>(value), Pal.Result<int>())));
                            if (EqualityComparer<TValue>.Default.Equals(tvalue, entries[i].Value))
                            {
                                return i;
                            }
                        }
                    }
                }

                return -1;
            }

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList.Insert(int index, object? value) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList.Remove(object? value) => throw new NotSupportedException();

            /// <inheritdoc/>
            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void IList.RemoveAt(int index) => throw new NotSupportedException();

            /// <inheritdoc/>
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

                ThrowIfNegative(index);

                if (array.Length - index < _dictionary.Count)
                {
                    throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall);
                }

                if (array is TValue[] values)
                {
                    CopyTo(values, index);
                }
                else
                {
                    try
                    {
                        if (array is not object?[] objects)
                        {
                            throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                        }

                        foreach (TValue value in this)
                        {
                            objects[index++] = value;
                        }
                    }
                    catch (ArrayTypeMismatchException)
                    {
                        throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                    }
                }
            }

            /// <summary>Enumerates the elements of a <see cref="OrderedDictionary{TKey, TValue}.ValueCollection"/>.</summary>
            public struct Enumerator : IEnumerator<TValue>
            {
                /// <summary>The dictionary's enumerator.</summary>
                private OrderedDictionary<TKey, TValue>.Enumerator _enumerator;

                /// <summary>Initialize the enumerator.</summary>
                [Ensures("@this._enumerator.SpecFresh && @this._enumerator.SpecIndex == 0")]
                internal Enumerator(OrderedDictionary<TKey, TValue> dictionary) => _enumerator = dictionary.GetEnumerator();

                /// <inheritdoc/>
                [Ensures("Pal.Same(Result, @this._enumerator.SpecCurrent.Value)")]
                public TValue Current => _enumerator.Current.Value;

                /// <inheritdoc/>
                [Ensures("Pal.Boxes(Result, @this._enumerator.SpecCurrent.Value)")]
                object? IEnumerator.Current => Current;

                /// <inheritdoc/>
                [Requires("0 <= @this._enumerator.SpecIndex")]
                [Throws(typeof(InvalidOperationException), "!@this._enumerator.SpecFresh")]
                [Ensures("@this._enumerator.SpecFresh && 0 <= @this._enumerator.SpecIndex")]
                [Ensures("Result == (Pal.Old(@this._enumerator.SpecIndex) < @this._enumerator.SpecCount)")]
                [Ensures("Pal.Implies(Result, @this._enumerator.SpecIndex == Pal.Old(@this._enumerator.SpecIndex) + 1 && Pal.Old(@this._enumerator.SpecIndex) < @this._enumerator.SpecValues.Length && Pal.Same(@this._enumerator.SpecCurrent.Value, @this._enumerator.SpecValues[Pal.Old(@this._enumerator.SpecIndex)]))")]
                [Ensures("Pal.Implies(!Result, @this._enumerator.SpecIndex == Pal.Old(@this._enumerator.SpecIndex))")]
                public bool MoveNext() => _enumerator.MoveNext();

                /// <inheritdoc/>
                [Throws(typeof(InvalidOperationException), "!@this._enumerator.SpecFresh")]
                [Ensures("@this._enumerator.SpecFresh && @this._enumerator.SpecIndex == 0")]
                void IEnumerator.Reset() => EnumerableHelpers.Reset(ref _enumerator);

                /// <inheritdoc/>
                [Ensures("true")]
                readonly void IDisposable.Dispose() { }
            }
        }
    }

    /// <summary>Used to control behavior of insertion into a <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
    /// <remarks>Not nested in <see cref="OrderedDictionary{TKey, TValue}"/> to avoid multiple generic instantiations.</remarks>
    internal enum InsertionBehavior
    {
        /// <summary>Skip the insertion operation.</summary>
        IgnoreInsertion = 0,

        /// <summary>Specifies that an existing entry with the same key should be overwritten if encountered.</summary>
        OverwriteExisting = 1,

        /// <summary>Specifies that if an existing entry with the same key is encountered, an exception should be thrown.</summary>
        ThrowOnExisting = 2
    }
}
