// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Collections.ObjectModel;
using System.ComponentModel;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Serialization;
using PalLang;

namespace System.Collections.Generic
{
    /// <summary>The abstract state of a <see cref="Dictionary{TKey, TValue}"/>.</summary>
    [Spec]
    public struct DictionaryModel<TKey, TValue>
    {
        public SpecInt Count;
        /// <summary>The live keys, in entry order.</summary>
        public Seq<TKey> Keys;
        /// <summary>The live values, in entry order: <c>Values[p]</c> is <c>Keys[p]</c>'s.</summary>
        public Seq<TValue> Values;
        /// <summary>The comparer the dictionary was built with; null means the default comparer.</summary>
        public IEqualityComparer<TKey>? Comparer;
        /// <summary>The modification counter an enumerator checks.</summary>
        public SpecInt Version;
        /// <summary>The entries in use, live or free.</summary>
        public SpecInt Slots;
        /// <summary>The length of the entries array: how many entries fit without a resize.</summary>
        public SpecInt Capacity;
        /// <summary><c>Prefixes[i]</c> is the live key/value pairs among the first <c>i</c> entries, for <c>0 &lt;= i &lt;= Slots</c>.</summary>
        public Seq<Seq<KeyValuePair<TKey, TValue>>> Prefixes;
    }

    [DebuggerTypeProxy(typeof(IDictionaryDebugView<,>))]
    [DebuggerDisplay("Count = {Count}")]
    [Serializable]
    [TypeForwardedFrom("mscorlib, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    [Invariant("0 <= _freeCount && _freeCount <= _count && _count <= _entries.Length")]
    [Invariant("(_buckets == null) == (_entries == null)")]
    [Invariant("_buckets.Length == _entries.Length")]
    [Invariant("_entries != null || _count == 0")]
    [Invariant("_entries != null || _entries.Length == 0")]
    [Invariant("_entries == null || _entries.Length > 0")]
    [Invariant("_entries == null || _entries.Length <= Array.MaxLength")]
    [Invariant("_entries == null || System.Collections.HashHelpers.PrimeSize(_entries.Length)")]
    [Invariant("typeof(TKey).IsValueType || _comparer != null")]
    [Invariant("_buckets == null || Dictionary<TKey, TValue>.Wf(Contents(_buckets), Contents(_entries), _count, _freeList, _freeCount, _comparer)")]
    public class Dictionary<TKey, TValue> : IDictionary<TKey, TValue>, IDictionary, IReadOnlyDictionary<TKey, TValue>, ISerializable, IDeserializationCallback where TKey : notnull
    {
        // constants for serialization
        private const string VersionName = "Version"; // Do not rename (binary serialization)
        private const string HashSizeName = "HashSize"; // Do not rename (binary serialization). Must save buckets.Length
        private const string KeyValuePairsName = "KeyValuePairs"; // Do not rename (binary serialization)
        private const string ComparerName = "Comparer"; // Do not rename (binary serialization)

        private int[]? _buckets;
        private Entry[]? _entries;
#if TARGET_64BIT
        private ulong _fastModMultiplier;
#endif
        private int _count;
        private int _freeList;
        private int _freeCount;
        [Wrapping] private int _version;
        private IEqualityComparer<TKey>? _comparer;
        private KeyCollection? _keys;
        private ValueCollection? _values;
        private const int StartOfFreeList = -3;

        [Model]
        private DictionaryModel<TKey, TValue> Model => new DictionaryModel<TKey, TValue>
        {
            Count = _count - _freeCount,
            Keys = KeysOf(Pal.Contents(_entries), _count),
            Values = ValuesOf(Pal.Contents(_entries), _count),
            Comparer = _comparer,
            Version = _version,
            Slots = _count,
            Capacity = Pal.Contents(_entries).Length,
            Prefixes = PrefixesOf(Pal.Contents(_entries), _count),
        };

        [Spec]
        public SpecInt SpecCount => Model.Count;

        /// <summary>The keys, in entry order.</summary>
        [Spec]
        public Seq<TKey> SpecKeys => Model.Keys;

        /// <summary>The values, in entry order: <c>SpecValues[p]</c> is <c>SpecKeys[p]</c>'s.</summary>
        [Spec]
        public Seq<TValue> SpecValues => Model.Values;

        /// <summary>The comparer the dictionary was built with.</summary>
        [Spec]
        public IEqualityComparer<TKey>? SpecComparer => Model.Comparer;

        [Spec]
        public SpecInt SpecVersion => Model.Version;

        [Spec]
        public SpecInt SpecSlots => Model.Slots;

        [Spec]
        public SpecInt SpecCapacity => Model.Capacity;

        /// <summary>The prefixes an enumerator walks through (<see cref="DictionaryModel{TKey, TValue}.Prefixes"/>).</summary>
        [Spec]
        public Seq<Seq<KeyValuePair<TKey, TValue>>> SpecPrefixes => Model.Prefixes;

        [Spec]
        [PulseBody("DictionaryChain.prefixes $(entries) $(count)")]
        private static Seq<Seq<KeyValuePair<TKey, TValue>>> PrefixesOf(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        /// <summary>The keys of <paramref name="pairs"/>.</summary>
        [Spec]
        [PulseBody("DictionaryChain.firsts $(pairs)")]
        public static Seq<TKey> Firsts(Seq<KeyValuePair<TKey, TValue>> pairs) => throw new InvalidOperationException();

        /// <summary>The values of <paramref name="pairs"/>.</summary>
        [Spec]
        [PulseBody("DictionaryChain.seconds $(pairs)")]
        public static Seq<TValue> Seconds(Seq<KeyValuePair<TKey, TValue>> pairs) => throw new InvalidOperationException();

        // The hash table's theory (pal/Dictionary/DictionaryChain.fst, Pulse.Lib.CSharp.HashChain).
        [Spec]
        [PulseBody("DictionaryChain.wf $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        private static bool Wf(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.keys $(entries) $(count)")]
        private static Seq<TKey> KeysOf(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.values $(entries) $(count)")]
        private static Seq<TValue> ValuesOf(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        /// <summary>Some key of <paramref name="keys"/> is equal to <paramref name="key"/> at <paramref name="comparer"/>.</summary>
        [Spec]
        [PulseBody("DictionaryChain.mem $(comparer) $(keys) $(key)")]
        public static bool Mem(IEqualityComparer<TKey>? comparer, Seq<TKey> keys, TKey key) => throw new InvalidOperationException();

        /// <summary>At some position, <paramref name="keys"/> holds a key equal to <paramref name="key"/> and <paramref name="values"/> holds <paramref name="value"/>.</summary>
        [Spec]
        [PulseBody("DictionaryChain.maps $(comparer) $(keys) $(values) $(key) $(value)")]
        public static bool Maps(IEqualityComparer<TKey>? comparer, Seq<TKey> keys, Seq<TValue> values, TKey key, TValue value) => throw new InvalidOperationException();

        /// <summary>The hash code TryInsert stores for <paramref name="key"/>.</summary>
        [Spec]
        [PulseBody("U32.v (FStar.Int.Cast.int32_to_uint32 (Pulse.Lib.CSharp.Equality.hash (DictionaryChain.eff $(comparer)) $(key)))")]
        private static SpecInt HashCodeOf(IEqualityComparer<TKey>? comparer, TKey key) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.bucket $(buckets) $(entries) $(comparer) $(key)")]
        private static SpecInt Bucket(Seq<int> buckets, Seq<Entry> entries, IEqualityComparer<TKey>? comparer, TKey key) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.search $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q)")]
        private static bool Search(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.hit $(entries) $(comparer) $(key) $(i)")]
        private static bool Hit(Seq<Entry> entries, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Wf(buckets, entries, count, freeList, freeCount, comparer) && entries.Length > 0")]
        [Ensures("Dictionary<TKey, TValue>.Search(buckets, entries, count, freeList, freeCount, comparer, key, Dictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) - 1, 0)")]
        [Ensures("0 <= Dictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) && Dictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) <= entries.Length")]
        [PulseBody("DictionaryChain.search_start $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key)")]
        [Conditional("PAL")]
        private static void SearchStart(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Search(buckets, entries, count, freeList, freeCount, comparer, key, i, q)")]
        [Requires("0 <= i && i < entries.Length && !Dictionary<TKey, TValue>.Hit(entries, comparer, key, i)")]
        [Ensures("Dictionary<TKey, TValue>.Search(buckets, entries, count, freeList, freeCount, comparer, key, entries[i].next, q + 1)")]
        [Ensures("q + 1 <= entries.Length")]
        [PulseBody("DictionaryChain.search_step $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchStep(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Search(buckets, entries, count, freeList, freeCount, comparer, key, i, q)")]
        [Requires("Dictionary<TKey, TValue>.Hit(entries, comparer, key, i)")]
        [Ensures("Dictionary<TKey, TValue>.Mem(comparer, Dictionary<TKey, TValue>.KeysOf(entries, count), key)")]
        [Ensures("Dictionary<TKey, TValue>.Maps(comparer, Dictionary<TKey, TValue>.KeysOf(entries, count), Dictionary<TKey, TValue>.ValuesOf(entries, count), key, entries[i].value)")]
        [Ensures("0 <= i && i < count")]
        [PulseBody("DictionaryChain.search_hit $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchHit(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Search(buckets, entries, count, freeList, freeCount, comparer, key, i, q)")]
        [Requires("!(0 <= i && i < entries.Length)")]
        [Ensures("!Dictionary<TKey, TValue>.Mem(comparer, Dictionary<TKey, TValue>.KeysOf(entries, count), key)")]
        [PulseBody("DictionaryChain.search_absent $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchAbsent(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q) { }

        [Spec]
        [PulseBody("DictionaryChain.search_last $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q) $(last)")]
        private static bool SearchLast(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q, SpecInt last) => throw new InvalidOperationException();

        /// <summary><paramref name="keys1"/>/<paramref name="values1"/> are <paramref name="keys"/>/<paramref name="values"/> without the pair at one position, whose key is equal to <paramref name="key"/> and whose value is <paramref name="value"/>.</summary>
        [Spec]
        [PulseBody("DictionaryChain.removed $(comparer) $(keys) $(values) $(keys1) $(values1) $(key) $(value)")]
        public static bool Removed(IEqualityComparer<TKey>? comparer, Seq<TKey> keys, Seq<TValue> values, Seq<TKey> keys1, Seq<TValue> values1, TKey key, TValue value) => throw new InvalidOperationException();

        /// <summary><paramref name="keys1"/>/<paramref name="values1"/> are <paramref name="keys"/>/<paramref name="values"/> without the pair of one key equal to <paramref name="key"/>.</summary>
        [Spec]
        [PulseBody("DictionaryChain.removed_any $(comparer) $(keys) $(values) $(keys1) $(values1) $(key)")]
        public static bool RemovedAny(IEqualityComparer<TKey>? comparer, Seq<TKey> keys, Seq<TValue> values, Seq<TKey> keys1, Seq<TValue> values1, TKey key) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Removed(comparer, keys, values, keys1, values1, key, value)")]
        [Ensures("Dictionary<TKey, TValue>.RemovedAny(comparer, keys, values, keys1, values1, key)")]
        [PulseBody("DictionaryChain.removed_forget $(comparer) $(keys) $(values) $(keys1) $(values1) $(key) $(value)")]
        [Conditional("PAL")]
        private static void RemovedForget(IEqualityComparer<TKey>? comparer, Seq<TKey> keys, Seq<TValue> values, Seq<TKey> keys1, Seq<TValue> values1, TKey key, TValue value) { }

        // `(uint)hashCode % buckets.Length` is computed in `long`; its quotient fits.
        [Lemma]
        [Requires("0 <= a && 0 < b")]
        [Ensures("0 <= a / b && a / b <= a")]
        [PulseBody("DictionaryChain.div_fits $(a) $(b)")]
        [Conditional("PAL")]
        private static void DivFits(SpecInt a, SpecInt b) { }

        [Spec]
        [PulseBody("DictionaryChain.remove_writes $(buckets) $(buckets1) $(entries) $(entries1) $(comparer) $(key) $(freeList) $(i) $(last)")]
        private static bool RemoveWrites(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1, IEqualityComparer<TKey>? comparer, TKey key, SpecInt freeList, SpecInt i, SpecInt last) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Wf(buckets, entries, count, freeList, freeCount, comparer) && entries.Length > 0")]
        [Ensures("Dictionary<TKey, TValue>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, key, Dictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) - 1, 0, -1)")]
        [Ensures("0 <= Dictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) && Dictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) <= entries.Length")]
        [PulseBody("DictionaryChain.search_last_start $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key)")]
        [Conditional("PAL")]
        private static void SearchLastStart(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, key, i, q, last)")]
        [Requires("0 <= i && i < entries.Length && !Dictionary<TKey, TValue>.Hit(entries, comparer, key, i)")]
        [Ensures("Dictionary<TKey, TValue>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, key, entries[i].next, q + 1, i)")]
        [Ensures("q + 1 <= entries.Length")]
        [PulseBody("DictionaryChain.search_last_step $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q) $(last)")]
        [Conditional("PAL")]
        private static void SearchLastStep(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q, SpecInt last) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, key, i, q, last)")]
        [Requires("!(0 <= i && i < entries.Length)")]
        [Ensures("!Dictionary<TKey, TValue>.Mem(comparer, Dictionary<TKey, TValue>.KeysOf(entries, count), key)")]
        [PulseBody("DictionaryChain.search_last_absent $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q) $(last)")]
        [Conditional("PAL")]
        private static void SearchLastAbsent(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q, SpecInt last) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, key, i, q, last)")]
        [Requires("0 <= i && i < entries.Length")]
        [Ensures("-1 <= entries[i].next && entries[i].next < entries.Length")]
        [Ensures("-1 <= freeList && freeList < entries.Length")]
        [PulseBody("DictionaryChain.search_next $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q) $(last)")]
        [Conditional("PAL")]
        private static void SearchNext(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q, SpecInt last) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, key, i, q, last)")]
        [Requires("Dictionary<TKey, TValue>.Hit(entries, comparer, key, i)")]
        [Requires("Dictionary<TKey, TValue>.RemoveWrites(buckets, buckets1, entries, entries1, comparer, key, freeList, i, last)")]
        [Ensures("Dictionary<TKey, TValue>.Wf(buckets1, entries1, count, i, freeCount + 1, comparer) && freeCount + 1 <= count && 0 <= i && i < count")]
        [Ensures("Dictionary<TKey, TValue>.Mem(comparer, Dictionary<TKey, TValue>.KeysOf(entries, count), key)")]
        [Ensures("Dictionary<TKey, TValue>.Removed(comparer, Dictionary<TKey, TValue>.KeysOf(entries, count), Dictionary<TKey, TValue>.ValuesOf(entries, count), Dictionary<TKey, TValue>.KeysOf(entries1, count), Dictionary<TKey, TValue>.ValuesOf(entries1, count), key, entries[i].value)")]
        [PulseBody("DictionaryChain.remove_ok $(buckets) $(buckets1) $(entries) $(entries1) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(i) $(q) $(last)")]
        [Conditional("PAL")]
        private static void RemoveOk(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, SpecInt i, SpecInt q, SpecInt last) { }

        [Spec]
        [PulseBody("DictionaryChain.zeros $(buckets)")]
        private static bool Zeros(Seq<int> buckets) => throw new InvalidOperationException();

        [Lemma]
        [Requires("buckets.Length == entries.Length && Dictionary<TKey, TValue>.Zeros(buckets)")]
        [Ensures("Dictionary<TKey, TValue>.Wf(buckets, entries, 0, -1, 0, comparer) && Dictionary<TKey, TValue>.KeysOf(entries, 0) == Pal.EmptySeq<TKey>() && Dictionary<TKey, TValue>.ValuesOf(entries, 0) == Pal.EmptySeq<TValue>()")]
        [PulseBody("DictionaryChain.wf_fresh $(buckets) $(entries) $(comparer)")]
        [Conditional("PAL")]
        private static void WfFresh(Seq<int> buckets, Seq<Entry> entries, IEqualityComparer<TKey>? comparer) { }

        /// <summary>An empty table is well formed at any comparer (the constructors set it after <c>Initialize</c>).</summary>
        [Lemma]
        [Ensures("Pal.Implies(Dictionary<TKey, TValue>.Wf(buckets, entries, 0, freeList, 0, comparer), Dictionary<TKey, TValue>.Wf(buckets, entries, 0, freeList, 0, comparer2))")]
        [PulseBody("DictionaryChain.wf_rebind $(buckets) $(entries) $(freeList) $(comparer) $(comparer2)")]
        [Conditional("PAL")]
        private static void WfRebind(Seq<int> buckets, Seq<Entry> entries, SpecInt freeList, IEqualityComparer<TKey>? comparer, IEqualityComparer<TKey>? comparer2) { }

        /// <summary>
        /// Swapping a string dictionary's comparer for what <c>GetStringComparer</c> returned keeps
        /// its equality.
        /// </summary>
        [Spec]
        [PulseBody("DictionaryChain.string_swap_ok $(comparer)")]
        private static bool StringSwapOk(IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Ensures("Dictionary<TKey, TValue>.StringSwapOk(comparer)")]
        [PulseBody("DictionaryChain.string_swap $(comparer)")]
        [Conditional("PAL")]
        private static void StringSwap(IEqualityComparer<TKey>? comparer) { }

        /// <summary><paramref name="keys1"/>/<paramref name="values1"/> are <paramref name="keys"/>/<paramref name="values"/> with the pair (<paramref name="key"/>, <paramref name="value"/>) inserted at one position.</summary>
        [Spec]
        [PulseBody("DictionaryChain.added $(keys) $(values) $(keys1) $(values1) $(key) $(value)")]
        public static bool Added(Seq<TKey> keys, Seq<TValue> values, Seq<TKey> keys1, Seq<TValue> values1, TKey key, TValue value) => throw new InvalidOperationException();

        /// <summary><paramref name="values1"/> is <paramref name="values"/> with the value of one key equal to <paramref name="key"/> replaced by <paramref name="value"/>.</summary>
        [Spec]
        [PulseBody("DictionaryChain.overwritten $(comparer) $(keys) $(values) $(values1) $(key) $(value)")]
        public static bool Overwritten(IEqualityComparer<TKey>? comparer, Seq<TKey> keys, Seq<TValue> values, Seq<TValue> values1, TKey key, TValue value) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.fnext $(entries) $(i)")]
        private static SpecInt FNext(Seq<Entry> entries, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Wf(buckets, entries, count, freeList, freeCount, comparer) && entries.Length > 0")]
        [Ensures("0 <= Dictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) && Dictionary<TKey, TValue>.Bucket(buckets, entries, comparer, key) <= entries.Length")]
        [Ensures("Pal.Implies(freeCount > 0, 0 <= freeList && freeList < count && -1 <= Dictionary<TKey, TValue>.FNext(entries, freeList) && Dictionary<TKey, TValue>.FNext(entries, freeList) < count)")]
        [Ensures("Pal.Implies(freeCount == 0, freeList == -1) && freeCount <= count")]
        [PulseBody("DictionaryChain.insert_pre $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(key)")]
        [Conditional("PAL")]
        private static void InsertPre(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key) { }

        [Spec]
        [PulseBody("DictionaryChain.insert_writes $(buckets) $(buckets1) $(entries) $(entries1) $(comparer) $(key) $(value) $(i)")]
        private static bool InsertWrites(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1, IEqualityComparer<TKey>? comparer, TKey key, TValue value, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.InsertWrites(buckets, buckets1, entries, entries1, comparer, key, value, i) && key != null")]
        [Requires("(count1 == count && freeCount1 >= 0 && Dictionary<TKey, TValue>.Wf(buckets, entries, count, i, freeCount1 + 1, comparer) && freeList1 == Dictionary<TKey, TValue>.FNext(entries, i)) || (freeCount1 == 0 && i == count && count1 == count + 1 && Dictionary<TKey, TValue>.Wf(buckets, entries, count, freeList1, 0, comparer))")]
        [Ensures("Dictionary<TKey, TValue>.Wf(buckets1, entries1, count1, freeList1, freeCount1, comparer)")]
        [Ensures("Dictionary<TKey, TValue>.Added(Dictionary<TKey, TValue>.KeysOf(entries, count), Dictionary<TKey, TValue>.ValuesOf(entries, count), Dictionary<TKey, TValue>.KeysOf(entries1, count1), Dictionary<TKey, TValue>.ValuesOf(entries1, count1), key, value)")]
        [Ensures("Dictionary<TKey, TValue>.KeysOf(entries1, count1).Length == Dictionary<TKey, TValue>.KeysOf(entries, count).Length + 1")]
        [PulseBody("DictionaryChain.insert_ok $(buckets) $(buckets1) $(entries) $(entries1) $(count) $(count1) $(freeList1) $(freeCount1) $(i) $(comparer) $(key) $(value)")]
        [Conditional("PAL")]
        private static void InsertOk(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1, SpecInt count, SpecInt count1, SpecInt freeList1, SpecInt freeCount1, SpecInt i, IEqualityComparer<TKey>? comparer, TKey key, TValue value) { }

        [Spec]
        [PulseBody("DictionaryChain.overwrite_writes $(entries) $(entries1) $(i) $(value)")]
        private static bool OverwriteWrites(Seq<Entry> entries, Seq<Entry> entries1, SpecInt i, TValue value) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Search(buckets, entries, count, freeList, freeCount, comparer, key, i, q)")]
        [Requires("Dictionary<TKey, TValue>.Hit(entries, comparer, key, i)")]
        [Requires("Dictionary<TKey, TValue>.OverwriteWrites(entries, entries1, i, value)")]
        [Ensures("Dictionary<TKey, TValue>.Wf(buckets, entries1, count, freeList, freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(entries1, count) == Dictionary<TKey, TValue>.KeysOf(entries, count)")]
        [Ensures("Dictionary<TKey, TValue>.Overwritten(comparer, Dictionary<TKey, TValue>.KeysOf(entries, count), Dictionary<TKey, TValue>.ValuesOf(entries, count), Dictionary<TKey, TValue>.ValuesOf(entries1, count), key, value)")]
        [Ensures("Dictionary<TKey, TValue>.Mem(comparer, Dictionary<TKey, TValue>.KeysOf(entries, count), key)")]
        [PulseBody("DictionaryChain.overwrite_ok $(buckets) $(entries) $(entries1) $(count) $(freeList) $(freeCount) $(comparer) $(key) $(value) $(i) $(q)")]
        [Conditional("PAL")]
        private static void OverwriteOk(Seq<int> buckets, Seq<Entry> entries, Seq<Entry> entries1, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer, TKey key, TValue value, SpecInt i, SpecInt q) { }

        [Spec]
        [PulseBody("DictionaryChain.same_prefix $(old) $(entries) $(count)")]
        private static bool SamePrefix(Seq<Entry> old, Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.pre_wf $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        private static bool PreWf(Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Wf(buckets, old, count, freeList, freeCount, comparer) && Dictionary<TKey, TValue>.SamePrefix(old, entries, count)")]
        [Ensures("Dictionary<TKey, TValue>.PreWf(entries, count, freeList, freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(entries, count) == Dictionary<TKey, TValue>.KeysOf(old, count) && Dictionary<TKey, TValue>.ValuesOf(entries, count) == Dictionary<TKey, TValue>.ValuesOf(old, count)")]
        [PulseBody("DictionaryChain.copy_ok $(buckets) $(old) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void CopyOk(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer) { }

        [Spec]
        [PulseBody("DictionaryChain.rebuilt $(buckets) $(source) $(entries) $(count) $(i)")]
        private static bool Rebuilt(Seq<int> buckets, Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= count && count <= source.Length && source.Length > 0 && buckets.Length == source.Length && Dictionary<TKey, TValue>.Zeros(buckets)")]
        [Ensures("Dictionary<TKey, TValue>.Rebuilt(buckets, source, source, count, 0)")]
        [PulseBody("DictionaryChain.rebuild_start $(buckets) $(source) $(count)")]
        [Conditional("PAL")]
        private static void RebuildStart(Seq<int> buckets, Seq<Entry> source, SpecInt count) { }

        [Spec]
        [PulseBody("DictionaryChain.slot $(buckets) $(entries) $(i)")]
        private static SpecInt Slot(Seq<int> buckets, Seq<Entry> entries, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Rebuilt(buckets, source, entries, count, i) && i < count")]
        [Ensures("0 <= Dictionary<TKey, TValue>.Slot(buckets, entries, i) && Dictionary<TKey, TValue>.Slot(buckets, entries, i) <= entries.Length")]
        [PulseBody("DictionaryChain.rebuild_bucket $(buckets) $(source) $(entries) $(count) $(i)")]
        [Conditional("PAL")]
        private static void RebuildBucket(Seq<int> buckets, Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt i) { }

        [Spec]
        [PulseBody("DictionaryChain.link_writes $(buckets) $(buckets1) $(entries) $(entries1) $(i)")]
        private static bool LinkWrites(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Rebuilt(buckets, source, entries, count, i) && i < count && Dictionary<TKey, TValue>.LinkWrites(buckets, buckets1, entries, entries1, i)")]
        [Ensures("Dictionary<TKey, TValue>.Rebuilt(buckets1, source, entries1, count, i + 1)")]
        [PulseBody("DictionaryChain.rebuild_step $(buckets) $(buckets1) $(source) $(entries) $(entries1) $(count) $(i)")]
        [Conditional("PAL")]
        private static void RebuildStep(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> source, Seq<Entry> entries, Seq<Entry> entries1, SpecInt count, SpecInt i) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.PreWf(source, count, freeList, freeCount, comparer) && Dictionary<TKey, TValue>.Rebuilt(buckets, source, entries, count, count)")]
        [Ensures("Dictionary<TKey, TValue>.Wf(buckets, entries, count, freeList, freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(entries, count) == Dictionary<TKey, TValue>.KeysOf(source, count) && Dictionary<TKey, TValue>.ValuesOf(entries, count) == Dictionary<TKey, TValue>.ValuesOf(source, count)")]
        [PulseBody("DictionaryChain.rebuild_done $(buckets) $(source) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void RebuildDone(Seq<int> buckets, Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer) { }

        // Compacting into new arrays (`CopyEntries`, for `TrimExcess`).
        [Spec]
        [PulseBody("DictionaryChain.compactable $(old) $(count) $(comparer)")]
        private static bool Compactable(Seq<Entry> old, SpecInt count, IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Wf(buckets, old, count, freeList, freeCount, comparer) && 0 <= freeCount && freeCount <= count")]
        [Ensures("Dictionary<TKey, TValue>.Compactable(old, count, comparer) && Dictionary<TKey, TValue>.KeysOf(old, count).Length == count - freeCount")]
        [PulseBody("DictionaryChain.wf_compactable $(buckets) $(old) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void WfCompactable(Seq<int> buckets, Seq<Entry> old, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer) { }

        [Spec]
        [PulseBody("DictionaryChain.compacted $(buckets) $(old) $(entries) $(count) $(i) $(m) $(comparer)")]
        private static bool Compacted(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, SpecInt i, SpecInt m, IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Compactable(old, count, comparer) && entries.Length > 0 && buckets.Length == entries.Length && Dictionary<TKey, TValue>.Zeros(buckets) && Dictionary<TKey, TValue>.KeysOf(old, count).Length <= entries.Length")]
        [Ensures("Dictionary<TKey, TValue>.Compacted(buckets, old, entries, count, 0, 0, comparer)")]
        [PulseBody("DictionaryChain.compact_start $(buckets) $(old) $(entries) $(count) $(comparer)")]
        [Conditional("PAL")]
        private static void CompactStart(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, IEqualityComparer<TKey>? comparer) { }

        [Spec]
        [PulseBody("DictionaryChain.old_slot $(buckets) $(old) $(entries) $(i)")]
        private static SpecInt OldSlot(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Compacted(buckets, old, entries, count, i, m, comparer) && i < count && old[i].next >= -1")]
        [Ensures("0 <= m && m < entries.Length && 0 <= Dictionary<TKey, TValue>.OldSlot(buckets, old, entries, i) && Dictionary<TKey, TValue>.OldSlot(buckets, old, entries, i) <= entries.Length")]
        [PulseBody("DictionaryChain.compact_room $(buckets) $(old) $(entries) $(count) $(i) $(m) $(comparer)")]
        [Conditional("PAL")]
        private static void CompactRoom(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, SpecInt i, SpecInt m, IEqualityComparer<TKey>? comparer) { }

        [Spec]
        [PulseBody("DictionaryChain.compact_writes $(buckets) $(buckets1) $(old) $(entries) $(entries1) $(i) $(m) $(m1)")]
        private static bool CompactWrites(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> old, Seq<Entry> entries, Seq<Entry> entries1, SpecInt i, SpecInt m, SpecInt m1) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Compacted(buckets, old, entries, count, i, m, comparer) && i < count && Dictionary<TKey, TValue>.CompactWrites(buckets, buckets1, old, entries, entries1, i, m, m1)")]
        [Ensures("Dictionary<TKey, TValue>.Compacted(buckets1, old, entries1, count, i + 1, m1, comparer)")]
        [PulseBody("DictionaryChain.compact_step $(buckets) $(buckets1) $(old) $(entries) $(entries1) $(count) $(i) $(m) $(m1) $(comparer)")]
        [Conditional("PAL")]
        private static void CompactStep(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> old, Seq<Entry> entries, Seq<Entry> entries1, SpecInt count, SpecInt i, SpecInt m, SpecInt m1, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Compacted(buckets, old, entries, count, count, m, comparer)")]
        [Ensures("Dictionary<TKey, TValue>.Wf(buckets, entries, m, -1, 0, comparer) && Dictionary<TKey, TValue>.KeysOf(entries, m) == Dictionary<TKey, TValue>.KeysOf(old, count) && Dictionary<TKey, TValue>.ValuesOf(entries, m) == Dictionary<TKey, TValue>.ValuesOf(old, count) && m <= entries.Length && Dictionary<TKey, TValue>.KeysOf(entries, m).Length == m")]
        [PulseBody("DictionaryChain.compact_done $(buckets) $(old) $(entries) $(count) $(m) $(comparer)")]
        [Conditional("PAL")]
        private static void CompactDone(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, SpecInt m, IEqualityComparer<TKey>? comparer) { }

        [Spec]
        [PulseBody("DictionaryChain.non_randomized $(comparer)")]
        private static bool NonRandomized(IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.randomized $(comparer)")]
        private static IEqualityComparer<TKey>? Randomized(IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        /// <summary>Whether two comparers deem the same keys equal.</summary>
        [Spec]
        [PulseBody("DictionaryChain.same_equality $(comparer1) $(comparer2)")]
        public static bool SameEquality(IEqualityComparer<TKey>? comparer1, IEqualityComparer<TKey>? comparer2) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.NonRandomized(comparer)")]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(comparer, Dictionary<TKey, TValue>.Randomized(comparer)) && Dictionary<TKey, TValue>.Randomized(comparer) != null")]
        [PulseBody("DictionaryChain.randomized_same $(comparer)")]
        [Conditional("PAL")]
        private static void RandomizedSame(IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(comparer, comparer)")]
        [PulseBody("DictionaryChain.same_refl $(comparer)")]
        [Conditional("PAL")]
        private static void SameRefl(IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.SameEquality(comparer1, comparer2)")]
        [Ensures("Dictionary<TKey, TValue>.Mem(comparer1, keys, key) == Dictionary<TKey, TValue>.Mem(comparer2, keys, key)")]
        [PulseBody("DictionaryChain.mem_same $(comparer1) $(comparer2) $(keys) $(key)")]
        [Conditional("PAL")]
        public static void MemSame(IEqualityComparer<TKey>? comparer1, IEqualityComparer<TKey>? comparer2, Seq<TKey> keys, TKey key) { }

        [Spec]
        [PulseBody("DictionaryChain.rehashed $(source) $(entries) $(count) $(i) $(comparer)")]
        private static bool Rehashed(Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt i, IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        /// <summary>No live key of <paramref name="entries"/> is null.</summary>
        [Spec]
        [PulseBody("DictionaryChain.non_null (DictionaryChain.keys $(entries) $(count))")]
        private static bool NonNullKeys(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= count && count <= source.Length && Dictionary<TKey, TValue>.NonNullKeys(source, count)")]
        [Ensures("Dictionary<TKey, TValue>.Rehashed(source, source, count, 0, comparer)")]
        [PulseBody("DictionaryChain.rehash_start $(source) $(count) $(comparer)")]
        [Conditional("PAL")]
        private static void RehashStart(Seq<Entry> source, SpecInt count, IEqualityComparer<TKey>? comparer) { }

        [Spec]
        [PulseBody("DictionaryChain.rehash_writes $(entries) $(entries1) $(i) $(comparer)")]
        private static bool RehashWrites(Seq<Entry> entries, Seq<Entry> entries1, SpecInt i, IEqualityComparer<TKey>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.Rehashed(source, entries, count, i, comparer) && i < count && Dictionary<TKey, TValue>.RehashWrites(entries, entries1, i, comparer)")]
        [Ensures("Dictionary<TKey, TValue>.Rehashed(source, entries1, count, i + 1, comparer)")]
        [PulseBody("DictionaryChain.rehash_step $(source) $(entries) $(entries1) $(count) $(i) $(comparer)")]
        [Conditional("PAL")]
        private static void RehashStep(Seq<Entry> source, Seq<Entry> entries, Seq<Entry> entries1, SpecInt count, SpecInt i, IEqualityComparer<TKey>? comparer) { }

        /// <summary>The field <paramref name="field"/> holds the non-null comparer <paramref name="comparer"/>.</summary>
        [Spec]
        [PulseBody("($(field) == Some $(comparer))")]
        private static bool Holds(IEqualityComparer<TKey>? field, IEqualityComparer<TKey> comparer) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.pre_free $(entries) $(count) $(freeList) $(freeCount)")]
        private static bool PreFree(Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount) => throw new InvalidOperationException();

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.PreWf(entries, count, freeList, freeCount, comparer)")]
        [Ensures("Dictionary<TKey, TValue>.PreFree(entries, count, freeList, freeCount) && Dictionary<TKey, TValue>.NonNullKeys(entries, count)")]
        [PulseBody("DictionaryChain.pre_free_of $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void PreFreeOf(Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.PreFree(source, count, freeList, freeCount) && Dictionary<TKey, TValue>.Rehashed(source, entries, count, count, comparer)")]
        [Ensures("Dictionary<TKey, TValue>.PreWf(entries, count, freeList, freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(entries, count) == Dictionary<TKey, TValue>.KeysOf(source, count) && Dictionary<TKey, TValue>.ValuesOf(entries, count) == Dictionary<TKey, TValue>.ValuesOf(source, count)")]
        [PulseBody("DictionaryChain.rehash_done $(source) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void RehashDone(Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer) { }

        /// <summary>Some value of <paramref name="values"/> is equal to <paramref name="value"/> at <c>EqualityComparer&lt;TValue&gt;.Default</c> (a null <paramref name="value"/> matching null).</summary>
        [Spec]
        [PulseBody("DictionaryChain.has_value $(values) $(value)")]
        public static bool HasValue(Seq<TValue> values, TValue value) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.live_match $(entries) $(i) $(value)")]
        private static bool LiveMatch(Seq<Entry> entries, SpecInt i, TValue value) => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= i && i < entries.Length && !Dictionary<TKey, TValue>.HasValue(Dictionary<TKey, TValue>.ValuesOf(entries, i), value) && !Dictionary<TKey, TValue>.LiveMatch(entries, i, value)")]
        [Ensures("!Dictionary<TKey, TValue>.HasValue(Dictionary<TKey, TValue>.ValuesOf(entries, i + 1), value)")]
        [PulseBody("DictionaryChain.value_miss $(entries) $(i) $(value)")]
        [Conditional("PAL")]
        private static void ValueMiss(Seq<Entry> entries, SpecInt i, TValue value) { }

        [Lemma]
        [Requires("Dictionary<TKey, TValue>.LiveMatch(entries, i, value) && i < count && count <= entries.Length")]
        [Ensures("Dictionary<TKey, TValue>.HasValue(Dictionary<TKey, TValue>.ValuesOf(entries, count), value)")]
        [PulseBody("DictionaryChain.value_hit $(entries) $(i) $(count) $(value)")]
        [Conditional("PAL")]
        private static void ValueHit(Seq<Entry> entries, SpecInt i, SpecInt count, TValue value) { }

        /// <summary><paramref name="keys"/> and <paramref name="values"/> zipped into <see cref="KeyValuePair{TKey, TValue}"/>s.</summary>
        [Spec]
        [PulseBody("DictionaryChain.pairs $(keys) $(values)")]
        public static Seq<KeyValuePair<TKey, TValue>> Pairs(Seq<TKey> keys, Seq<TValue> values) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("DictionaryChain.entry_pairs $(entries) $(count)")]
        private static Seq<KeyValuePair<TKey, TValue>> EntryPairsOf(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= i && i < entries.Length")]
        [Ensures("Pal.Implies(entries[i].next >= -1, Dictionary<TKey, TValue>.EntryPairsOf(entries, i + 1) == Pal.Snoc(Dictionary<TKey, TValue>.EntryPairsOf(entries, i), new KeyValuePair<TKey, TValue>(entries[i].key, entries[i].value)))")]
        [Ensures("Pal.Implies(entries[i].next < -1, Dictionary<TKey, TValue>.EntryPairsOf(entries, i + 1) == Dictionary<TKey, TValue>.EntryPairsOf(entries, i))")]
        [PulseBody("DictionaryChain.pairs_step $(entries) $(i)")]
        [Conditional("PAL")]
        private static void PairsStep(Seq<Entry> entries, SpecInt i) { }

        [Lemma]
        [Requires("0 <= i && i < entries.Length")]
        [Ensures("Pal.Implies(entries[i].next >= -1, Dictionary<TKey, TValue>.KeysOf(entries, i + 1) == Pal.Snoc(Dictionary<TKey, TValue>.KeysOf(entries, i), entries[i].key))")]
        [Ensures("Pal.Implies(entries[i].next < -1, Dictionary<TKey, TValue>.KeysOf(entries, i + 1) == Dictionary<TKey, TValue>.KeysOf(entries, i))")]
        [PulseBody("DictionaryChain.keys_step $(entries) $(i)")]
        [Conditional("PAL")]
        private static void KeysStep(Seq<Entry> entries, SpecInt i) { }

        [Lemma]
        [Requires("0 <= i && i <= n && n <= entries.Length")]
        [Ensures("Dictionary<TKey, TValue>.KeysOf(entries, i).Length <= Dictionary<TKey, TValue>.KeysOf(entries, n).Length")]
        [Ensures("Dictionary<TKey, TValue>.KeysOf(entries, i) == Pal.Slice(Dictionary<TKey, TValue>.KeysOf(entries, n), 0, Dictionary<TKey, TValue>.KeysOf(entries, i).Length)")]
        [PulseBody("DictionaryChain.keys_prefix $(entries) $(i) $(n)")]
        [Conditional("PAL")]
        private static void KeysPrefix(Seq<Entry> entries, SpecInt i, SpecInt n) { }

        [Lemma]
        [Requires("0 <= i && i < entries.Length")]
        [Ensures("Pal.Implies(entries[i].next >= -1, Dictionary<TKey, TValue>.ValuesOf(entries, i + 1) == Pal.Snoc(Dictionary<TKey, TValue>.ValuesOf(entries, i), entries[i].value))")]
        [Ensures("Pal.Implies(entries[i].next < -1, Dictionary<TKey, TValue>.ValuesOf(entries, i + 1) == Dictionary<TKey, TValue>.ValuesOf(entries, i))")]
        [PulseBody("DictionaryChain.values_step $(entries) $(i)")]
        [Conditional("PAL")]
        private static void ValuesStep(Seq<Entry> entries, SpecInt i) { }

        [Lemma]
        [Requires("0 <= i && i <= n && n <= entries.Length")]
        [Ensures("Dictionary<TKey, TValue>.ValuesOf(entries, i).Length <= Dictionary<TKey, TValue>.ValuesOf(entries, n).Length")]
        [Ensures("Dictionary<TKey, TValue>.ValuesOf(entries, i) == Pal.Slice(Dictionary<TKey, TValue>.ValuesOf(entries, n), 0, Dictionary<TKey, TValue>.ValuesOf(entries, i).Length)")]
        [PulseBody("DictionaryChain.values_prefix $(entries) $(i) $(n)")]
        [Conditional("PAL")]
        private static void ValuesPrefix(Seq<Entry> entries, SpecInt i, SpecInt n) { }

        [Lemma]
        [Requires("0 <= i && i <= n && n <= entries.Length")]
        [Ensures("Dictionary<TKey, TValue>.EntryPairsOf(entries, i).Length <= Dictionary<TKey, TValue>.EntryPairsOf(entries, n).Length")]
        [Ensures("Dictionary<TKey, TValue>.EntryPairsOf(entries, i) == Pal.Slice(Dictionary<TKey, TValue>.EntryPairsOf(entries, n), 0, Dictionary<TKey, TValue>.EntryPairsOf(entries, i).Length)")]
        [PulseBody("DictionaryChain.pairs_prefix $(entries) $(i) $(n)")]
        [Conditional("PAL")]
        private static void PairsPrefix(Seq<Entry> entries, SpecInt i, SpecInt n) { }

        [Lemma]
        [Requires("0 <= freeCount && freeCount <= count && (count == 0 || Dictionary<TKey, TValue>.Wf(buckets, entries, count, freeList, freeCount, comparer))")]
        [Ensures("Dictionary<TKey, TValue>.EntryPairsOf(entries, count).Length == count - freeCount && Dictionary<TKey, TValue>.KeysOf(entries, count).Length == count - freeCount && Dictionary<TKey, TValue>.ValuesOf(entries, count).Length == count - freeCount")]
        [PulseBody("DictionaryChain.pairs_count $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void PairsCount(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<TKey>? comparer) { }

        [Ensures("@this.SpecCount == 0 && @this.SpecKeys == Pal.EmptySeq<TKey>() && @this.SpecValues == Pal.EmptySeq<TValue>() && @this.SpecSlots == 0 && @this.SpecVersion == 0")]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(null, @this.SpecComparer)")]
        public Dictionary() : this(0, null) { }

        [Requires("capacity <= 0x7FFFFFC3")]
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == 0 && @this.SpecKeys == Pal.EmptySeq<TKey>() && @this.SpecValues == Pal.EmptySeq<TValue>() && @this.SpecSlots == 0 && @this.SpecVersion == 0")]
        [Ensures("capacity <= @this.SpecCapacity && Dictionary<TKey, TValue>.SameEquality(null, @this.SpecComparer)")]
        public Dictionary(int capacity) : this(capacity, null) { }

        [Ensures("@this.SpecCount == 0 && @this.SpecKeys == Pal.EmptySeq<TKey>() && @this.SpecValues == Pal.EmptySeq<TValue>() && @this.SpecSlots == 0 && @this.SpecVersion == 0")]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(comparer, @this.SpecComparer)")]
        public Dictionary(IEqualityComparer<TKey>? comparer) : this(0, comparer) { }

        [Requires("capacity <= 0x7FFFFFC3")]
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == 0 && @this.SpecKeys == Pal.EmptySeq<TKey>() && @this.SpecValues == Pal.EmptySeq<TValue>() && @this.SpecSlots == 0 && @this.SpecVersion == 0")]
        [Ensures("capacity <= @this.SpecCapacity && Dictionary<TKey, TValue>.SameEquality(comparer, @this.SpecComparer)")]
        public Dictionary(int capacity, IEqualityComparer<TKey>? comparer)
        {
            if (capacity < 0)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.capacity);
            }

            if (capacity > 0)
            {
                Initialize(capacity);
            }

            // For reference types, we always want to store a comparer instance, either
            // the one provided, or if one wasn't provided, the default (accessing
            // EqualityComparer<TKey>.Default with shared generics on every dictionary
            // access can add measurable overhead).  For value types, if no comparer is
            // provided, or if the default is provided, we'd prefer to use
            // EqualityComparer<TKey>.Default.Equals on every use, enabling the JIT to
            // devirtualize and possibly inline the operation.
            if (!typeof(TKey).IsValueType)
            {
                _comparer = comparer ?? EqualityComparer<TKey>.Default;

                // Special-case EqualityComparer<string>.Default, StringComparer.Ordinal, and StringComparer.OrdinalIgnoreCase.
                // We use a non-randomized comparer for improved perf, falling back to a randomized comparer if the
                // hash buckets become unbalanced.
                if (typeof(TKey) == typeof(string) &&
                    NonRandomizedStringEqualityComparer.GetStringComparer(_comparer!) is IEqualityComparer<string> stringComparer)
                {
                    StringSwap(_comparer);
                    Pal.Assert(Dictionary<TKey, TValue>.SameEquality(comparer, _comparer));
                    _comparer = (IEqualityComparer<TKey>)stringComparer;
                    Pal.Assert(Dictionary<TKey, TValue>.SameEquality(comparer, _comparer));
                }
            }
            else if (comparer is not null && // first check for null to avoid forcing default comparer instantiation unnecessarily
                     comparer != EqualityComparer<TKey>.Default)
            {
                _comparer = comparer;
            }
            WfRebind(Pal.Contents(_buckets), Pal.Contents(_entries), _freeList, null, _comparer);
        }

        public Dictionary(IDictionary<TKey, TValue> dictionary) : this(dictionary, null) { }

        public Dictionary(IDictionary<TKey, TValue> dictionary, IEqualityComparer<TKey>? comparer) :
            this(dictionary?.Count ?? 0, comparer)
        {
            if (dictionary == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.dictionary);
            }

            AddRange(dictionary);
        }

        public Dictionary(IEnumerable<KeyValuePair<TKey, TValue>> collection) : this(collection, null) { }

        public Dictionary(IEnumerable<KeyValuePair<TKey, TValue>> collection, IEqualityComparer<TKey>? comparer) :
            this((collection as ICollection<KeyValuePair<TKey, TValue>>)?.Count ?? 0, comparer)
        {
            if (collection == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.collection);
            }

            AddRange(collection);
        }

        private void AddRange(IEnumerable<KeyValuePair<TKey, TValue>> enumerable)
        {
            // It is likely that the passed-in enumerable is Dictionary<TKey,TValue>. When this is the case,
            // avoid the enumerator allocation and overhead by looping through the entries array directly.
            // We only do this when dictionary is Dictionary<TKey,TValue> and not a subclass, to maintain
            // back-compat with subclasses that may have overridden the enumerator behavior.
            if (enumerable.GetType() == typeof(Dictionary<TKey, TValue>))
            {
                Dictionary<TKey, TValue> source = (Dictionary<TKey, TValue>)enumerable;

                if (source.Count == 0)
                {
                    // Nothing to copy, all done
                    return;
                }

                // This is not currently a true .AddRange as it needs to be an initialized dictionary
                // of the correct size, and also an empty dictionary with no current entities (and no argument checks).
                Debug.Assert(source._entries is not null);
                Debug.Assert(_entries is not null);
                Debug.Assert(_entries.Length >= source.Count);
                Debug.Assert(_count == 0);

                Entry[] oldEntries = source._entries;
                if (source._comparer == _comparer)
                {
                    // If comparers are the same, we can copy _entries without rehashing.
                    CopyEntries(oldEntries, source._count);
                    return;
                }

                // Comparers differ need to rehash all the entries via Add
                int count = source._count;
                for (int i = 0; i < count; i++)
                {
                    // Only copy if an entry
                    if (oldEntries[i].next >= -1)
                    {
                        Add(oldEntries[i].key, oldEntries[i].value);
                    }
                }
                return;
            }

            // We similarly special-case KVP<>[] and List<KVP<>>, as they're commonly used to seed dictionaries, and
            // we want to avoid the enumerator costs (e.g. allocation) for them as well. Extract a span if possible.
            ReadOnlySpan<KeyValuePair<TKey, TValue>> span;
            if (enumerable is KeyValuePair<TKey, TValue>[] array)
            {
                span = array;
            }
            else if (enumerable.GetType() == typeof(List<KeyValuePair<TKey, TValue>>))
            {
                span = CollectionsMarshal.AsSpan((List<KeyValuePair<TKey, TValue>>)enumerable);
            }
            else
            {
                // Fallback path for all other enumerables
                foreach (KeyValuePair<TKey, TValue> pair in enumerable)
                {
                    Add(pair.Key, pair.Value);
                }
                return;
            }

            // We got a span. Add the elements to the dictionary.
            foreach (KeyValuePair<TKey, TValue> pair in span)
            {
                Add(pair.Key, pair.Value);
            }
        }

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        [EditorBrowsable(EditorBrowsableState.Never)]
        protected Dictionary(SerializationInfo info, StreamingContext context)
        {
            // We can't do anything with the keys and values until the entire graph has been deserialized
            // and we have a resonable estimate that GetHashCode is not going to fail.  For the time being,
            // we'll just cache this.  The graph is not valid until OnDeserialization has been called.
            HashHelpers.SerializationInfoTable.Add(this, info);
        }

        [Ensures("Dictionary<TKey, TValue>.SameEquality(Result, @this.SpecComparer)")]
        public IEqualityComparer<TKey> Comparer
        {
            get
            {
                if (typeof(TKey) == typeof(string))
                {
                    Debug.Assert(_comparer is not null, "The comparer should never be null for a reference type.");
                    return (IEqualityComparer<TKey>)IInternalStringEqualityComparer.GetUnderlyingEqualityComparer((IEqualityComparer<string?>)_comparer);
                }
                else
                {
                    return _comparer ?? EqualityComparer<TKey>.Default;
                }
            }
        }

        [Ensures("Result == @this.SpecCount")]
        public int Count => _count - _freeCount;

        /// <summary>
        /// Gets the total numbers of elements the internal data structure can hold without resizing.
        /// </summary>
        [Ensures("Result == @this.SpecCapacity")]
        public int Capacity => _entries?.Length ?? 0;

        [Ensures("ReferenceEquals(Result._dictionary, @this)")]
        public KeyCollection Keys => _keys ??= new KeyCollection(this);

        ICollection<TKey> IDictionary<TKey, TValue>.Keys => Keys;

        IEnumerable<TKey> IReadOnlyDictionary<TKey, TValue>.Keys => Keys;

        [Ensures("ReferenceEquals(Result._dictionary, @this)")]
        public ValueCollection Values => _values ??= new ValueCollection(this);

        ICollection<TValue> IDictionary<TKey, TValue>.Values => Values;

        IEnumerable<TValue> IReadOnlyDictionary<TKey, TValue>.Values => Values;

        public TValue this[TKey key]
        {
            [Throws(typeof(ArgumentNullException), "key == null")]
            [Throws(typeof(KeyNotFoundException), "key != null && !Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
            [Ensures("Dictionary<TKey, TValue>.Maps(@this.SpecComparer, @this.SpecKeys, @this.SpecValues, key, Result)")]
            get
            {
                ref TValue value = ref FindValue(key);
                if (!Unsafe.IsNullRef(ref value))
                {
                    return value;
                }

                ThrowHelper.ThrowKeyNotFoundException(key);
                return default;
            }
            [Requires("@this.SpecSlots < 0x7FFFFFC3")]
            [Throws(typeof(ArgumentNullException), "key == null")]
            [Ensures("Pal.Implies(!Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key), Dictionary<TKey, TValue>.Added(Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecKeys, @this.SpecValues, key, value) && @this.SpecCount == Old(@this.SpecCount) + 1)")]
            [Ensures("Pal.Implies(Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key), @this.SpecKeys == Old(@this.SpecKeys) && @this.SpecCount == Old(@this.SpecCount) && Dictionary<TKey, TValue>.Overwritten(Old(@this.SpecComparer), Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecValues, key, value))")]
            [Ensures("Dictionary<TKey, TValue>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
            set
            {
                bool modified = TryInsert(key, value, InsertionBehavior.OverwriteExisting);
                Debug.Assert(modified);
            }
        }

        [Requires("@this.SpecSlots < 0x7FFFFFC3")]
        [Throws(typeof(ArgumentNullException), "key == null")]
        [Throws(typeof(ArgumentException), "key != null && Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        [Ensures("!Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key) && Dictionary<TKey, TValue>.Added(Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecKeys, @this.SpecValues, key, value) && @this.SpecCount == Old(@this.SpecCount) + 1")]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        public void Add(TKey key, TValue value)
        {
            bool modified = TryInsert(key, value, InsertionBehavior.ThrowOnExisting);
            Debug.Assert(modified); // If there was an existing key and the Add failed, an exception will already have been thrown.
        }

        [Requires("@this.SpecSlots < 0x7FFFFFC3")]
        [Throws(typeof(ArgumentNullException), "keyValuePair.Key == null")]
        [Throws(typeof(ArgumentException), "keyValuePair.Key != null && Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, keyValuePair.Key)")]
        [Ensures("!Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), keyValuePair.Key) && Dictionary<TKey, TValue>.Added(Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecKeys, @this.SpecValues, keyValuePair.Key, keyValuePair.Value) && @this.SpecCount == Old(@this.SpecCount) + 1")]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        void ICollection<KeyValuePair<TKey, TValue>>.Add(KeyValuePair<TKey, TValue> keyValuePair) =>
            Add(keyValuePair.Key, keyValuePair.Value);

        [Throws(typeof(ArgumentNullException), "keyValuePair.Key == null")]
        [Ensures("Pal.Implies(Result, Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, keyValuePair.Key))")]
        [Ensures("Pal.Implies(!Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, keyValuePair.Key), !Result)")]
        bool ICollection<KeyValuePair<TKey, TValue>>.Contains(KeyValuePair<TKey, TValue> keyValuePair)
        {
            ref TValue value = ref FindValue(keyValuePair.Key);
            if (!Unsafe.IsNullRef(ref value) && EqualityComparer<TValue>.Default.Equals(value, keyValuePair.Value))
            {
                return true;
            }

            return false;
        }

        [Throws(typeof(ArgumentNullException), "keyValuePair.Key == null")]
        [Ensures("Pal.Implies(Result, Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), keyValuePair.Key) && Dictionary<TKey, TValue>.RemovedAny(Old(@this.SpecComparer), Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecKeys, @this.SpecValues, keyValuePair.Key) && @this.SpecCount == Old(@this.SpecCount) - 1)")]
        [Ensures("Pal.Implies(!Result, @this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecCount == Old(@this.SpecCount))")]
        [Ensures("Pal.Implies(!Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), keyValuePair.Key), !Result)")]
        [Ensures("@this.SpecComparer == Old(@this.SpecComparer)")]
        bool ICollection<KeyValuePair<TKey, TValue>>.Remove(KeyValuePair<TKey, TValue> keyValuePair)
        {
            ref TValue value = ref FindValue(keyValuePair.Key);
            if (!Unsafe.IsNullRef(ref value) && EqualityComparer<TValue>.Default.Equals(value, keyValuePair.Value))
            {
                Remove(keyValuePair.Key);
                return true;
            }

            return false;
        }

        [Ensures("@this.SpecCount == 0 && @this.SpecKeys == Pal.EmptySeq<TKey>() && @this.SpecValues == Pal.EmptySeq<TValue>()")]
        [Ensures("@this.SpecComparer == Old(@this.SpecComparer) && @this.SpecVersion == Old(@this.SpecVersion)")]
        public void Clear()
        {
            int count = _count;
            if (count > 0)
            {
                Debug.Assert(_buckets != null, "_buckets should be non-null");
                Debug.Assert(_entries != null, "_entries should be non-null");

                Array.Clear(_buckets);

                _count = 0;
                _freeList = -1;
                _freeCount = 0;
                Array.Clear(_entries, 0, count);
            }
        }

        [Throws(typeof(ArgumentNullException), "key == null")]
        [Ensures("Result == Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        public bool ContainsKey(TKey key) =>
            !Unsafe.IsNullRef(ref FindValue(key));

        [Ensures("Result == Dictionary<TKey, TValue>.HasValue(@this.SpecValues, value)")]
        public bool ContainsValue(TValue value)
        {
            Entry[]? entries = _entries;
            if (value == null)
            {
                for (int i = 0; i < _count; i++)
                {
                    Pal.Invariant(0 <= i && i <= _count && (entries != null || _count == 0));
                    Pal.Invariant(!HasValue(ValuesOf(Pal.Contents(entries), i), value));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && HasValue(ValuesOf(Pal.Contents(entries), _count), value)));
                    if (entries![i].next >= -1 && entries[i].value == null)
                    {
                        ValueHit(Pal.Contents(entries), i, _count, value);
                        return true;
                    }
                    ValueMiss(Pal.Contents(entries), i, value);
                }
            }
            else if (typeof(TValue).IsValueType)
            {
                // ValueType: Devirtualize with EqualityComparer<TValue>.Default intrinsic
                for (int i = 0; i < _count; i++)
                {
                    Pal.Invariant(0 <= i && i <= _count && (entries != null || _count == 0));
                    Pal.Invariant(!HasValue(ValuesOf(Pal.Contents(entries), i), value));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && HasValue(ValuesOf(Pal.Contents(entries), _count), value)));
                    if (entries![i].next >= -1 && EqualityComparer<TValue>.Default.Equals(entries[i].value, value))
                    {
                        ValueHit(Pal.Contents(entries), i, _count, value);
                        return true;
                    }
                    ValueMiss(Pal.Contents(entries), i, value);
                }
            }
            else
            {
                // Object type: Shared Generic, EqualityComparer<TValue>.Default won't devirtualize
                // https://github.com/dotnet/runtime/issues/10050
                // So cache in a local rather than get EqualityComparer per loop iteration
                EqualityComparer<TValue> defaultComparer = EqualityComparer<TValue>.Default;
                for (int i = 0; i < _count; i++)
                {
                    Pal.Invariant(0 <= i && i <= _count && (entries != null || _count == 0));
                    Pal.Invariant(!HasValue(ValuesOf(Pal.Contents(entries), i), value));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && HasValue(ValuesOf(Pal.Contents(entries), _count), value)));
                    if (entries![i].next >= -1 && defaultComparer.Equals(entries[i].value, value))
                    {
                        ValueHit(Pal.Contents(entries), i, _count, value);
                        return true;
                    }
                    ValueMiss(Pal.Contents(entries), i, value);
                }
            }

            return false;
        }

        [Requires("array != null && index >= 0")]
        [Throws(typeof(ArgumentException), "index > Pal.Contents(array).Length || Pal.Contents(array).Length - index < @this.SpecCount")]
        [Ensures("@this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecVersion == Pal.Old(@this.SpecVersion)")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("@this.SpecKeys.Length == @this.SpecCount")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.SpecKeys.Length, Dictionary<TKey, TValue>.Pairs(@this.SpecKeys, @this.SpecValues))")]
        [Rlimit(4)]
        private void CopyTo(KeyValuePair<TKey, TValue>[] array, int index)
        {
            if (array == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.array);
            }

            if ((uint)index > (uint)array.Length)
            {
                ThrowHelper.ThrowArgumentOutOfRange_IndexMustBeLessOrEqualException();
            }

            if (array.Length - index < Count)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_ArrayPlusOffTooSmall);
            }

            PairsCount(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, _comparer);
            int count = _count;
            Entry[]? entries = _entries;
            Ghost<Seq<KeyValuePair<TKey, TValue>>> array0 = Pal.Contents(array);
            Ghost<int> index0 = index;
            PairsPrefix(Pal.Contents(entries), 0, count);
            for (int i = 0; i < count; i++)
            {
                Pal.Invariant(0 <= i && i <= count && count == _count && (entries != null || count == 0));
                Pal.Invariant(index == index0.Value + EntryPairsOf(Pal.Contents(entries), i).Length);
                Pal.Invariant(index0.Value + EntryPairsOf(Pal.Contents(entries), count).Length <= array0.Value.Length);
                Pal.Invariant(Pal.Contents(array).Length == array0.Value.Length);
                Pal.Invariant(Pal.Contents(array) == Pal.Splice(array0.Value, index0.Value, index, EntryPairsOf(Pal.Contents(entries), i)));
                Pal.Invariant(EntryPairsOf(Pal.Contents(entries), i).Length <= EntryPairsOf(Pal.Contents(entries), count).Length);
                Pal.Invariant(EntryPairsOf(Pal.Contents(entries), i) == Pal.Slice(EntryPairsOf(Pal.Contents(entries), count), 0, EntryPairsOf(Pal.Contents(entries), i).Length));
                PairsStep(Pal.Contents(entries), i);
                PairsPrefix(Pal.Contents(entries), i + 1, count);
                if (entries![i].next >= -1)
                {
                    array[index++] = new KeyValuePair<TKey, TValue>(entries[i].key, entries[i].value);
                }
            }
        }

        [Ensures("ReferenceEquals(Result._dictionary, @this) && Result._version == @this.SpecVersion && Result._index == 0 && Result._getEnumeratorRetType == Dictionary<TKey, TValue>.Enumerator.KeyValuePair")]
        public Enumerator GetEnumerator() => new Enumerator(this, Enumerator.KeyValuePair);

        [Ensures("Pal.Implies(@this.SpecCount != 0, Pal.Exists((Dictionary<TKey, TValue>.Enumerator e) => Pal.Boxes(Result, e) && " +
            "ReferenceEquals(e._dictionary, @this) && e._version == @this.SpecVersion && e._index == 0 && e._getEnumeratorRetType == Dictionary<TKey, TValue>.Enumerator.KeyValuePair))")]
        IEnumerator<KeyValuePair<TKey, TValue>> IEnumerable<KeyValuePair<TKey, TValue>>.GetEnumerator() =>
            Count == 0 ? GenericEmptyEnumerator<KeyValuePair<TKey, TValue>>.Instance :
            GetEnumerator();

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        [EditorBrowsable(EditorBrowsableState.Never)]
        public virtual void GetObjectData(SerializationInfo info, StreamingContext context)
        {
            if (info == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.info);
            }

            info.AddValue(VersionName, _version);
            info.AddValue(ComparerName, Comparer, typeof(IEqualityComparer<TKey>));
            info.AddValue(HashSizeName, _buckets == null ? 0 : _buckets.Length); // This is the length of the bucket array

            if (_buckets != null)
            {
                var array = new KeyValuePair<TKey, TValue>[Count];
                CopyTo(array, 0);
                info.AddValue(KeyValuePairsName, array, typeof(KeyValuePair<TKey, TValue>[]));
            }
        }

        [Throws(typeof(ArgumentNullException), "key == null")]
        [Ensures("Pal.Iff(Unsafe.IsNullRef(ref Result), !Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key))")]
        [Ensures("Pal.Implies(!Unsafe.IsNullRef(ref Result), Dictionary<TKey, TValue>.Maps(@this.SpecComparer, @this.SpecKeys, @this.SpecValues, key, Result))")]
        internal ref TValue FindValue(TKey key)
        {
            if (key == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
            }

            ref Entry entry = ref Unsafe.NullRef<Entry>();
            if (_buckets != null)
            {
                Debug.Assert(_entries != null, "expected entries to be != null");
                IEqualityComparer<TKey>? comparer = _comparer;
                if (typeof(TKey).IsValueType && // comparer can only be null for value types; enable JIT to eliminate entire if block for ref types
                    comparer == null)
                {
                    // TODO: Replace with just key.GetHashCode once https://github.com/dotnet/runtime/issues/117521 is resolved.
                    uint hashCode = (uint)EqualityComparer<TKey>.Default.GetHashCode(key);
                    SearchStart(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, comparer, key);
                    int i = GetBucket(hashCode);
                    Entry[]? entries = _entries;
                    uint collisionCount = 0;

                    // ValueType: Devirtualize with EqualityComparer<TKey>.Default intrinsic
                    i--; // Value in _buckets is 1-based; subtract 1 from i. We do it here so it fuses with the following conditional.
                    do
                    {
                        Pal.Invariant(collisionCount <= (uint)entries.Length && Pal.Broke() == Pal.Returned());
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount)));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Iff(Unsafe.IsNullRef(ref Pal.ResultRef<TValue>()), !Dictionary<TKey, TValue>.Mem(comparer, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count), key))));
                        Pal.Invariant(Pal.Implies(Pal.Returned() && !Unsafe.IsNullRef(ref Pal.ResultRef<TValue>()), Dictionary<TKey, TValue>.Maps(comparer, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key, Pal.ResultRef<TValue>())));
                        Pal.Decreases((uint)entries.Length - collisionCount);
                        // Test in if to drop range check for following array access
                        if ((uint)i >= (uint)entries.Length)
                        {
                            SearchAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                            goto ReturnNotFound;
                        }

                        entry = ref entries[i];
                        if (entry.hashCode == hashCode && EqualityComparer<TKey>.Default.Equals(entry.key, key))
                        {
                            SearchHit(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                            goto ReturnFound;
                        }

                        SearchStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                        i = entry.next;

                        collisionCount++;
                    } while (collisionCount <= (uint)entries.Length);

                    // The chain of entries forms a loop; which means a concurrent update has happened.
                    // Break out of the loop and throw, rather than looping forever.
                    goto ConcurrentOperation;
                }
                else
                {
                    Debug.Assert(comparer is not null);
                    uint hashCode = (uint)comparer.GetHashCode(key);
                    SearchStart(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, comparer, key);
                    int i = GetBucket(hashCode);
                    Entry[]? entries = _entries;
                    uint collisionCount = 0;
                    i--; // Value in _buckets is 1-based; subtract 1 from i. We do it here so it fuses with the following conditional.
                    do
                    {
                        Pal.Invariant(collisionCount <= (uint)entries.Length && Pal.Broke() == Pal.Returned());
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount)));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Iff(Unsafe.IsNullRef(ref Pal.ResultRef<TValue>()), !Dictionary<TKey, TValue>.Mem(comparer, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count), key))));
                        Pal.Invariant(Pal.Implies(Pal.Returned() && !Unsafe.IsNullRef(ref Pal.ResultRef<TValue>()), Dictionary<TKey, TValue>.Maps(comparer, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key, Pal.ResultRef<TValue>())));
                        Pal.Decreases((uint)entries.Length - collisionCount);
                        // Test in if to drop range check for following array access
                        if ((uint)i >= (uint)entries.Length)
                        {
                            SearchAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                            goto ReturnNotFound;
                        }

                        entry = ref entries[i];
                        if (entry.hashCode == hashCode && comparer.Equals(entry.key, key))
                        {
                            SearchHit(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                            goto ReturnFound;
                        }

                        SearchStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                        i = entry.next;

                        collisionCount++;
                    } while (collisionCount <= (uint)entries.Length);

                    // The chain of entries forms a loop; which means a concurrent update has happened.
                    // Break out of the loop and throw, rather than looping forever.
                    goto ConcurrentOperation;
                }
            }

            goto ReturnNotFound;

        ConcurrentOperation:
            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
        ReturnFound:
            ref TValue value = ref entry.value;
        Return:
            return ref value;
        ReturnNotFound:
            value = ref Unsafe.NullRef<TValue>();
            goto Return;
        }

        // [Open] (R27.23, R33.15): the constructor calls it before it sets `_comparer`, where the
        // invariant does not hold yet.
        [Open]
        [Requires("0 <= capacity && capacity <= 0x7FFFFFC3 && @this._buckets == null && @this._entries == null && @this._count == 0 && @this._freeCount == 0")]
        [Requires("Pal.Contents(@this._buckets).Length == 0 && Pal.Contents(@this._entries).Length == 0")]
        [Ensures("@this._buckets != null && @this._entries != null")]
        [Ensures("capacity <= Result && 0 < Result && Result == Pal.Contents(@this._entries).Length && Pal.Contents(@this._buckets).Length == Result && Result <= Array.MaxLength && System.Collections.HashHelpers.PrimeSize(Result)")]
        [Ensures("Dictionary<TKey, TValue>.Wf(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count, @this._freeList, @this._freeCount, @this._comparer)")]
        [Ensures("Dictionary<TKey, TValue>.KeysOf(Pal.Contents(@this._entries), @this._count) == Pal.EmptySeq<TKey>() && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(@this._entries), @this._count) == Pal.EmptySeq<TValue>()")]
        private int Initialize(int capacity)
        {
            int size = HashHelpers.GetPrime(capacity);
            int[] buckets = new int[size];
            Entry[] entries = new Entry[size];
            WfFresh(Pal.Contents(buckets), Pal.Contents(entries), _comparer);

            // Assign member variables after both arrays allocated to guard against corruption from OOM if second fails
            _freeList = -1;
#if TARGET_64BIT
            _fastModMultiplier = HashHelpers.GetFastModMultiplier((uint)size);
#endif
            _buckets = buckets;
            _entries = entries;

            return size;
        }

        [Requires("@this.SpecSlots < 0x7FFFFFC3")]
        [Throws(typeof(ArgumentNullException), "key == null")]
        [Throws(typeof(ArgumentException), "key != null && behavior == InsertionBehavior.ThrowOnExisting && Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        [Ensures("Pal.Implies(!Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key), Result && Dictionary<TKey, TValue>.Added(Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecKeys, @this.SpecValues, key, value) && @this.SpecCount == Old(@this.SpecCount) + 1)")]
        [Ensures("Pal.Implies(Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key), @this.SpecKeys == Old(@this.SpecKeys) && @this.SpecCount == Old(@this.SpecCount))")]
        [Ensures("Pal.Implies(Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key) && behavior == InsertionBehavior.OverwriteExisting, Result && Dictionary<TKey, TValue>.Overwritten(Old(@this.SpecComparer), Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecValues, key, value))")]
        [Ensures("Pal.Implies(Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key) && behavior != InsertionBehavior.OverwriteExisting, !Result && @this.SpecValues == Old(@this.SpecValues) && behavior != InsertionBehavior.ThrowOnExisting)")]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        [OpaqueSpecs("Search", "Wf", "Mem", "Overwritten")]
        private bool TryInsert(TKey key, TValue value, InsertionBehavior behavior)
        {
            // NOTE: this method is mirrored in CollectionsMarshal.GetValueRefOrAddDefault below.
            // If you make any changes here, make sure to keep that version in sync as well.

            if (key == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
            }

            Ghost<Seq<TKey>> keys0 = KeysOf(Pal.Contents(_entries), _count);
            Ghost<Seq<TValue>> values0 = ValuesOf(Pal.Contents(_entries), _count);
            Ghost<int> live0 = _count - _freeCount;
            if (_buckets == null)
            {
                Initialize(0);
                Pal.Assert(KeysOf(Pal.Contents(_entries), _count) == keys0.Value && ValuesOf(Pal.Contents(_entries), _count) == values0.Value && _count - _freeCount == live0.Value);
            }
            Pal.Join(_buckets != null && _entries != null && _buckets.Length == _entries.Length && 0 < _entries.Length && _entries.Length <= Array.MaxLength && System.Collections.HashHelpers.PrimeSize(_entries.Length));
            Pal.Join(0 <= _freeCount && _freeCount <= _count && _count <= _entries.Length && _count < 0x7FFFFFC3);
            Pal.Join(_comparer == Pal.Old(this.SpecComparer) && (typeof(TKey).IsValueType || _comparer != null));
            Pal.Join(Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, _comparer));
            Pal.Join(KeysOf(Pal.Contents(_entries), _count) == keys0.Value && ValuesOf(Pal.Contents(_entries), _count) == values0.Value && _count - _freeCount == live0.Value);
            Pal.Join(keys0.Value == Pal.Old(this.SpecKeys) && values0.Value == Pal.Old(this.SpecValues) && live0.Value == Pal.Old(this.SpecCount) && key != null && !Pal.Returned());
            Pal.Split();
            Debug.Assert(_buckets != null);

            Entry[]? entries = _entries;
            Debug.Assert(entries != null, "expected entries to be non-null");

            IEqualityComparer<TKey>? comparer = _comparer;
            Debug.Assert(comparer is not null || typeof(TKey).IsValueType);
            uint hashCode = (uint)((typeof(TKey).IsValueType && comparer == null) ? key.GetHashCode() : comparer!.GetHashCode(key));
            Pal.Assert(KeysOf(Pal.Contents(entries), _count) == keys0.Value && ValuesOf(Pal.Contents(entries), _count) == values0.Value && _count - _freeCount == live0.Value);

            uint collisionCount = 0;
            SearchStart(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key);
            ref int bucket = ref GetBucket(hashCode);
            int i = bucket - 1; // Value in _buckets is 1-based

            if (typeof(TKey).IsValueType && // comparer can only be null for value types; enable JIT to eliminate entire if block for ref types
                comparer == null)
            {
                // ValueType: Devirtualize with EqualityComparer<TKey>.Default intrinsic
                while ((uint)i < (uint)entries.Length)
                {
                    Pal.Invariant(collisionCount <= (uint)entries.Length && _entries == entries && _comparer == comparer && _count - _freeCount == live0.Value);
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer) && Dictionary<TKey, TValue>.Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.Mem(comparer, keys0.Value, key)));
                    Pal.Invariant(Pal.Implies(Pal.Returned() && behavior == InsertionBehavior.OverwriteExisting, Pal.Result<bool>() && Dictionary<TKey, TValue>.Overwritten(comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key, value)));
                    Pal.Invariant(Pal.Implies(Pal.Returned() && behavior != InsertionBehavior.OverwriteExisting, !Pal.Result<bool>() && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && behavior != InsertionBehavior.ThrowOnExisting));
                    Pal.Decreases((uint)entries.Length - collisionCount);
                    Ghost<Seq<Entry>> c0 = Pal.Contents(entries);
                    if (entries[i].hashCode == hashCode && EqualityComparer<TKey>.Default.Equals(entries[i].key, key))
                    {
                        SearchHit(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                        if (behavior == InsertionBehavior.OverwriteExisting)
                        {
                            Ghost<Seq<Entry>> before = Pal.Contents(entries);
                            entries[i].value = value;
                            OverwriteOk(Pal.Contents(_buckets), before.Value, Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, value, i, collisionCount);
                            return true;
                        }

                        if (behavior == InsertionBehavior.ThrowOnExisting)
                        {
                            ThrowHelper.ThrowAddingDuplicateWithKeyArgumentException(key);
                        }

                        return false;
                    }
                    Pal.Join(Pal.Implies(!Pal.Returned(), Pal.Contents(entries) == c0.Value && !Dictionary<TKey, TValue>.Hit(Pal.Contents(entries), comparer, key, i)));
                    Pal.Join(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.Mem(comparer, keys0.Value, key)));
                    Pal.Join(Pal.Implies(Pal.Returned() && behavior == InsertionBehavior.OverwriteExisting, Pal.Result<bool>() && Dictionary<TKey, TValue>.Overwritten(comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key, value)));
                    Pal.Join(Pal.Implies(Pal.Returned() && behavior != InsertionBehavior.OverwriteExisting, !Pal.Result<bool>() && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && behavior != InsertionBehavior.ThrowOnExisting));

                    SearchStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                    i = entries[i].next;

                    collisionCount++;
                    if (collisionCount > (uint)entries.Length)
                    {
                        // The chain of entries forms a loop; which means a concurrent update has happened.
                        // Break out of the loop and throw, rather than looping forever.
                        ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                    }
                }
                SearchAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
            }
            else
            {
                Debug.Assert(comparer is not null);
                while ((uint)i < (uint)entries.Length)
                {
                    Pal.Invariant(collisionCount <= (uint)entries.Length && _entries == entries && _comparer == comparer && _count - _freeCount == live0.Value);
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer) && Dictionary<TKey, TValue>.Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.Mem(comparer, keys0.Value, key)));
                    Pal.Invariant(Pal.Implies(Pal.Returned() && behavior == InsertionBehavior.OverwriteExisting, Pal.Result<bool>() && Dictionary<TKey, TValue>.Overwritten(comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key, value)));
                    Pal.Invariant(Pal.Implies(Pal.Returned() && behavior != InsertionBehavior.OverwriteExisting, !Pal.Result<bool>() && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && behavior != InsertionBehavior.ThrowOnExisting));
                    Pal.Decreases((uint)entries.Length - collisionCount);
                    Ghost<Seq<Entry>> c0 = Pal.Contents(entries);
                    if (entries[i].hashCode == hashCode && comparer.Equals(entries[i].key, key))
                    {
                        SearchHit(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                        if (behavior == InsertionBehavior.OverwriteExisting)
                        {
                            Ghost<Seq<Entry>> before = Pal.Contents(entries);
                            entries[i].value = value;
                            OverwriteOk(Pal.Contents(_buckets), before.Value, Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, value, i, collisionCount);
                            return true;
                        }

                        if (behavior == InsertionBehavior.ThrowOnExisting)
                        {
                            ThrowHelper.ThrowAddingDuplicateWithKeyArgumentException(key);
                        }

                        return false;
                    }
                    Pal.Join(Pal.Implies(!Pal.Returned(), Pal.Contents(entries) == c0.Value && !Dictionary<TKey, TValue>.Hit(Pal.Contents(entries), comparer, key, i)));
                    Pal.Join(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.Mem(comparer, keys0.Value, key)));
                    Pal.Join(Pal.Implies(Pal.Returned() && behavior == InsertionBehavior.OverwriteExisting, Pal.Result<bool>() && Dictionary<TKey, TValue>.Overwritten(comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key, value)));
                    Pal.Join(Pal.Implies(Pal.Returned() && behavior != InsertionBehavior.OverwriteExisting, !Pal.Result<bool>() && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && behavior != InsertionBehavior.ThrowOnExisting));

                    SearchStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
                    i = entries[i].next;

                    collisionCount++;
                    if (collisionCount > (uint)entries.Length)
                    {
                        // The chain of entries forms a loop; which means a concurrent update has happened.
                        // Break out of the loop and throw, rather than looping forever.
                        ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                    }
                }
                SearchAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount);
            }
            Pal.Join(collisionCount <= (uint)entries.Length && _entries == entries && _comparer == comparer && _count - _freeCount == live0.Value);
            Pal.Join(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer) && Dictionary<TKey, TValue>.Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount) && !Dictionary<TKey, TValue>.Mem(comparer, keys0.Value, key) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value));
            Pal.Join(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.Mem(comparer, keys0.Value, key)));
            Pal.Join(Pal.Implies(Pal.Returned() && behavior == InsertionBehavior.OverwriteExisting, Pal.Result<bool>() && Dictionary<TKey, TValue>.Overwritten(comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key, value)));
            Pal.Join(Pal.Implies(Pal.Returned() && behavior != InsertionBehavior.OverwriteExisting, !Pal.Result<bool>() && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && behavior != InsertionBehavior.ThrowOnExisting));
            Pal.Join(keys0.Value == Pal.Old(this.SpecKeys) && values0.Value == Pal.Old(this.SpecValues) && live0.Value == Pal.Old(this.SpecCount) && comparer == Pal.Old(this.SpecComparer));
            Pal.Join(_buckets != null && _entries != null && _buckets.Length == _entries.Length && 0 < _entries.Length && _entries.Length <= Array.MaxLength && System.Collections.HashHelpers.PrimeSize(_entries.Length));
            Pal.Join(0 <= _freeCount && _freeCount <= _count && _count <= _entries.Length && _count < 0x7FFFFFC3 && (typeof(TKey).IsValueType || comparer != null));
            Pal.Join(key != null && hashCode == Dictionary<TKey, TValue>.HashCodeOf(comparer, key) && Pal.Index(bucket) == hashCode % _buckets.Length);
            Pal.Split();

            Ghost<int> count0 = _count;
            InsertPre(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key);
            int index;
            if (_freeCount > 0)
            {
                index = _freeList;
                Debug.Assert((StartOfFreeList - entries[_freeList].next) >= -1, "shouldn't overflow because `next` cannot underflow");
                _freeList = StartOfFreeList - entries[_freeList].next;
                _freeCount--;
                Pal.Assert(_count == count0.Value && _freeCount >= 0 && Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), count0.Value, index, _freeCount + 1, comparer) && _freeList == Dictionary<TKey, TValue>.FNext(Pal.Contents(entries), index));
                Pal.Assert(0 <= index && index < entries.Length);
            }
            else
            {
                int count = _count;
                if (count == entries.Length)
                {
                    Resize();
                    Pal.Assert(_count == count && count < _entries.Length);
                    Pal.Assert(_buckets != null && _buckets.Length > 0);
                    DivFits(hashCode, _buckets.Length);
                    bucket = ref GetBucket(hashCode);
                    InsertPre(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, comparer, key);
                    Pal.Assert(count < _entries.Length);
                }
                Pal.Join(_buckets != null && _entries != null && _buckets.Length == _entries.Length && 0 < _entries.Length && _entries.Length <= Array.MaxLength && System.Collections.HashHelpers.PrimeSize(_entries.Length));
                Pal.Join(_freeCount == 0 && _count == count && count == count0.Value && count < _entries.Length && _comparer == comparer && _count - _freeCount == live0.Value);
                Pal.Join(Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(_entries), count, _freeList, 0, comparer));
                Pal.Join(Pal.Index(bucket) == hashCode % _buckets.Length && 0 <= Dictionary<TKey, TValue>.Bucket(Pal.Contents(_buckets), Pal.Contents(_entries), comparer, key) && Dictionary<TKey, TValue>.Bucket(Pal.Contents(_buckets), Pal.Contents(_entries), comparer, key) <= _entries.Length);
                Pal.Join(KeysOf(Pal.Contents(_entries), count) == keys0.Value && ValuesOf(Pal.Contents(_entries), count) == values0.Value);
                index = count;
                _count = count + 1;
                entries = _entries;
                Pal.Assert(_freeCount == 0 && index == count0.Value && _count == count0.Value + 1 && Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), count0.Value, _freeList, 0, comparer));
                Pal.Assert(0 <= index && index < entries.Length);
            }
            Pal.Join(_buckets != null && _entries != null && _buckets.Length == _entries.Length && 0 < _entries.Length && _entries.Length <= Array.MaxLength && System.Collections.HashHelpers.PrimeSize(_entries.Length));
            Pal.Join(0 <= _freeCount && _freeCount <= _count && _count <= _entries.Length && entries == _entries && _comparer == comparer);
            Pal.Join(0 <= index && index < entries.Length && Pal.Index(bucket) == hashCode % _buckets.Length && 0 <= Dictionary<TKey, TValue>.Bucket(Pal.Contents(_buckets), Pal.Contents(entries), comparer, key) && Dictionary<TKey, TValue>.Bucket(Pal.Contents(_buckets), Pal.Contents(entries), comparer, key) <= entries.Length);
            Pal.Join((_count == count0.Value && _freeCount >= 0 && Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), count0.Value, index, _freeCount + 1, comparer) && _freeList == Dictionary<TKey, TValue>.FNext(Pal.Contents(entries), index)) || (_freeCount == 0 && index == count0.Value && _count == count0.Value + 1 && Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), count0.Value, _freeList, 0, comparer)));
            Pal.Join(KeysOf(Pal.Contents(entries), count0.Value) == keys0.Value && ValuesOf(Pal.Contents(entries), count0.Value) == values0.Value && _count - _freeCount == live0.Value + 1);

            Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
            Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
            ref Entry entry = ref entries![index];
            entry.hashCode = hashCode;
            entry.next = bucket - 1; // Value in _buckets is 1-based
            entry.key = key;
            entry.value = value;
            bucket = index + 1; // Value in _buckets is 1-based
            _version++;
            InsertOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), count0.Value, _count, _freeList, _freeCount, index, comparer, key, value);
            Pal.Assert(Dictionary<TKey, TValue>.Added(keys0.Value, values0.Value, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(_entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(_entries), _count), key, value));
            Pal.Assert(_comparer == comparer && _count - _freeCount == live0.Value + 1);
            SameRefl(comparer);

            // Value types never rehash
            if (!typeof(TKey).IsValueType && collisionCount > HashHelpers.HashCollisionThreshold && comparer is NonRandomizedStringEqualityComparer)
            {
                // If we hit the collision threshold we'll need to switch to the comparer which is using randomized string hashing
                // i.e. EqualityComparer<string>.Default.
                Resize(entries.Length, true);
                Pal.Assert(Dictionary<TKey, TValue>.Added(keys0.Value, values0.Value, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(_entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(_entries), _count), key, value) && Dictionary<TKey, TValue>.SameEquality(comparer, _comparer) && _count - _freeCount == live0.Value + 1);
            }
            Pal.Assert(Dictionary<TKey, TValue>.Added(keys0.Value, values0.Value, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(_entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(_entries), _count), key, value));
            Pal.Assert(Dictionary<TKey, TValue>.SameEquality(comparer, _comparer) && _count - _freeCount == live0.Value + 1);

            return true;
        }

        /// <summary>
        /// Gets an instance of a type that may be used to perform operations on the current <see cref="Dictionary{TKey, TValue}"/>
        /// using a <typeparamref name="TAlternateKey"/> as a key instead of a <typeparamref name="TKey"/>.
        /// </summary>
        /// <typeparam name="TAlternateKey">The alternate type of a key for performing lookups.</typeparam>
        /// <returns>The created lookup instance.</returns>
        /// <exception cref="InvalidOperationException">The dictionary's comparer is not compatible with <typeparamref name="TAlternateKey"/>.</exception>
        /// <remarks>
        /// The dictionary must be using a comparer that implements <see cref="IAlternateEqualityComparer{TAlternateKey, TKey}"/> with
        /// <typeparamref name="TAlternateKey"/> and <typeparamref name="TKey"/>. If it doesn't, an exception will be thrown.
        /// </remarks>
        public AlternateLookup<TAlternateKey> GetAlternateLookup<TAlternateKey>()
            where TAlternateKey : notnull, allows ref struct
        {
            if (!AlternateLookup<TAlternateKey>.IsCompatibleKey(this))
            {
                ThrowHelper.ThrowInvalidOperationException(ExceptionResource.InvalidOperation_IncompatibleComparer);
            }

            return new AlternateLookup<TAlternateKey>(this);
        }

        /// <summary>
        /// Gets an instance of a type that may be used to perform operations on the current <see cref="Dictionary{TKey, TValue}"/>
        /// using a <typeparamref name="TAlternateKey"/> as a key instead of a <typeparamref name="TKey"/>.
        /// </summary>
        /// <typeparam name="TAlternateKey">The alternate type of a key for performing lookups.</typeparam>
        /// <param name="lookup">The created lookup instance when the method returns true, or a default instance that should not be used if the method returns false.</param>
        /// <returns>true if a lookup could be created; otherwise, false.</returns>
        /// <remarks>
        /// The dictionary must be using a comparer that implements <see cref="IAlternateEqualityComparer{TAlternateKey, TKey}"/> with
        /// <typeparamref name="TAlternateKey"/> and <typeparamref name="TKey"/>. If it doesn't, the method will return false.
        /// </remarks>
        public bool TryGetAlternateLookup<TAlternateKey>(
            out AlternateLookup<TAlternateKey> lookup)
            where TAlternateKey : notnull, allows ref struct
        {
            if (AlternateLookup<TAlternateKey>.IsCompatibleKey(this))
            {
                lookup = new AlternateLookup<TAlternateKey>(this);
                return true;
            }

            lookup = default;
            return false;
        }

        /// <summary>
        /// Provides a type that may be used to perform operations on a <see cref="Dictionary{TKey, TValue}"/>
        /// using a <typeparamref name="TAlternateKey"/> as a key instead of a <typeparamref name="TKey"/>.
        /// </summary>
        /// <typeparam name="TAlternateKey">The alternate type of a key for performing lookups.</typeparam>
        public readonly struct AlternateLookup<TAlternateKey> where TAlternateKey : notnull, allows ref struct
        {
            /// <summary>Initialize the instance. The dictionary must have already been verified to have a compatible comparer.</summary>
            internal AlternateLookup(Dictionary<TKey, TValue> dictionary)
            {
                Debug.Assert(dictionary is not null);
                Debug.Assert(IsCompatibleKey(dictionary));
                Dictionary = dictionary;
            }

            /// <summary>Gets the <see cref="Dictionary{TKey, TValue}"/> against which this instance performs operations.</summary>
            public Dictionary<TKey, TValue> Dictionary { get; }

            /// <summary>Gets or sets the value associated with the specified alternate key.</summary>
            /// <param name="key">The alternate key of the value to get or set.</param>
            /// <value>
            /// The value associated with the specified alternate key. If the specified alternate key is not found, a get operation throws
            /// a <see cref="KeyNotFoundException"/>, and a set operation creates a new element with the specified key.
            /// </value>
            /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
            /// <exception cref="KeyNotFoundException">The property is retrieved and alternate key does not exist in the collection.</exception>
            public TValue this[TAlternateKey key]
            {
                get
                {
                    ref TValue value = ref FindValue(key, out _);
                    if (Unsafe.IsNullRef(ref value))
                    {
                        ThrowHelper.ThrowKeyNotFoundException(GetAlternateComparer(Dictionary).Create(key));
                    }

                    return value;
                }
                set => GetValueRefOrAddDefault(key, out _) = value;
            }

            /// <summary>Checks whether the dictionary has a comparer compatible with <typeparamref name="TAlternateKey"/>.</summary>
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            internal static bool IsCompatibleKey(Dictionary<TKey, TValue> dictionary)
            {
                Debug.Assert(dictionary is not null);
                return dictionary._comparer is IAlternateEqualityComparer<TAlternateKey, TKey>;
            }

            /// <summary>Gets the dictionary's alternate comparer. The dictionary must have already been verified as compatible.</summary>
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            internal static IAlternateEqualityComparer<TAlternateKey, TKey> GetAlternateComparer(Dictionary<TKey, TValue> dictionary)
            {
                Debug.Assert(IsCompatibleKey(dictionary));
                return Unsafe.As<IAlternateEqualityComparer<TAlternateKey, TKey>>(dictionary._comparer)!;
            }

            /// <summary>Gets the value associated with the specified alternate key.</summary>
            /// <param name="key">The alternate key of the value to get.</param>
            /// <param name="value">
            /// When this method returns, contains the value associated with the specified key, if the key is found;
            /// otherwise, the default value for the type of the value parameter.
            /// </param>
            /// <returns><see langword="true"/> if an entry was found; otherwise, <see langword="false"/>.</returns>
            /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
            public bool TryGetValue(TAlternateKey key, [MaybeNullWhen(false)] out TValue value)
            {
                ref TValue valueRef = ref FindValue(key, out _);
                if (!Unsafe.IsNullRef(ref valueRef))
                {
                    value = valueRef;
                    return true;
                }

                value = default;
                return false;
            }

            /// <summary>Gets the value associated with the specified alternate key.</summary>
            /// <param name="key">The alternate key of the value to get.</param>
            /// <param name="actualKey">
            /// When this method returns, contains the actual key associated with the alternate key, if the key is found;
            /// otherwise, the default value for the type of the key parameter.
            /// </param>
            /// <param name="value">
            /// When this method returns, contains the value associated with the specified key, if the key is found;
            /// otherwise, the default value for the type of the value parameter.
            /// </param>
            /// <returns><see langword="true"/> if an entry was found; otherwise, <see langword="false"/>.</returns>
            /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
            public bool TryGetValue(TAlternateKey key, [MaybeNullWhen(false)] out TKey actualKey, [MaybeNullWhen(false)] out TValue value)
            {
                ref TValue valueRef = ref FindValue(key, out actualKey);
                if (!Unsafe.IsNullRef(ref valueRef))
                {
                    value = valueRef;
                    Debug.Assert(actualKey is not null);
                    return true;
                }

                value = default;
                return false;
            }

            /// <summary>Determines whether the <see cref="Dictionary{TKey, TValue}"/> contains the specified alternate key.</summary>
            /// <param name="key">The alternate key to check.</param>
            /// <returns><see langword="true"/> if the key is in the dictionary; otherwise, <see langword="false"/>.</returns>
            /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
            public bool ContainsKey(TAlternateKey key) =>
                !Unsafe.IsNullRef(ref FindValue(key, out _));

            /// <summary>Finds the entry associated with the specified alternate key.</summary>
            /// <param name="key">The alternate key.</param>
            /// <param name="actualKey">The actual key, if found.</param>
            /// <returns>A reference to the value associated with the key, if found; otherwise, a null reference.</returns>
            internal ref TValue FindValue(TAlternateKey key, [MaybeNullWhen(false)] out TKey actualKey)
            {
                Dictionary<TKey, TValue> dictionary = Dictionary;
                IAlternateEqualityComparer<TAlternateKey, TKey> comparer = GetAlternateComparer(dictionary);

                ref Entry entry = ref Unsafe.NullRef<Entry>();
                if (dictionary._buckets != null)
                {
                    Debug.Assert(dictionary._entries != null, "expected entries to be != null");

                    uint hashCode = (uint)comparer.GetHashCode(key);
                    int i = dictionary.GetBucket(hashCode);
                    Entry[]? entries = dictionary._entries;
                    uint collisionCount = 0;
                    i--; // Value in _buckets is 1-based; subtract 1 from i. We do it here so it fuses with the following conditional.
                    do
                    {
                        // Should be a while loop https://github.com/dotnet/runtime/issues/9422
                        // Test in if to drop range check for following array access
                        if ((uint)i >= (uint)entries.Length)
                        {
                            goto ReturnNotFound;
                        }

                        entry = ref entries[i];
                        if (entry.hashCode == hashCode && comparer.Equals(key, entry.key))
                        {
                            goto ReturnFound;
                        }

                        i = entry.next;

                        collisionCount++;
                    } while (collisionCount <= (uint)entries.Length);

                    // The chain of entries forms a loop; which means a concurrent update has happened.
                    // Break out of the loop and throw, rather than looping forever.
                    goto ConcurrentOperation;
                }

                goto ReturnNotFound;

            ConcurrentOperation:
                ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
            ReturnFound:
                ref TValue value = ref entry.value;
                actualKey = entry.key;
            Return:
                return ref value;
            ReturnNotFound:
                value = ref Unsafe.NullRef<TValue>();
                actualKey = default!;
                goto Return;
            }

            /// <summary>Removes the value with the specified alternate key from the <see cref="Dictionary{TKey, TValue}"/>.</summary>
            /// <param name="key">The alternate key of the element to remove.</param>
            /// <returns>true if the element is successfully found and removed; otherwise, false.</returns>
            /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
            public bool Remove(TAlternateKey key) =>
                Remove(key, out _, out _);

            /// <summary>
            /// Removes the value with the specified alternate key from the <see cref="Dictionary{TKey, TValue}"/>,
            /// and copies the element to the value parameter.
            /// </summary>
            /// <param name="key">The alternate key of the element to remove.</param>
            /// <param name="actualKey">The removed key.</param>
            /// <param name="value">The removed element.</param>
            /// <returns>true if the element is successfully found and removed; otherwise, false.</returns>
            /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
            public bool Remove(TAlternateKey key, [MaybeNullWhen(false)] out TKey actualKey, [MaybeNullWhen(false)] out TValue value)
            {
                Dictionary<TKey, TValue> dictionary = Dictionary;
                IAlternateEqualityComparer<TAlternateKey, TKey> comparer = GetAlternateComparer(dictionary);

                if (dictionary._buckets != null)
                {
                    Debug.Assert(dictionary._entries != null, "entries should be non-null");
                    uint collisionCount = 0;

                    uint hashCode = (uint)comparer.GetHashCode(key);

                    ref int bucket = ref dictionary.GetBucket(hashCode);
                    Entry[]? entries = dictionary._entries;
                    int last = -1;
                    int i = bucket - 1; // Value in buckets is 1-based
                    while ((uint)i < (uint)entries.Length)
                    {
                        ref Entry entry = ref entries[i];

                        if (entry.hashCode == hashCode && comparer.Equals(key, entry.key))
                        {
                            if (last < 0)
                            {
                                bucket = entry.next + 1; // Value in buckets is 1-based
                            }
                            else
                            {
                                entries[last].next = entry.next;
                            }

                            actualKey = entry.key;
                            value = entry.value;

                            Debug.Assert((StartOfFreeList - dictionary._freeList) < 0, "shouldn't underflow because max hashtable length is MaxPrimeArrayLength = 0x7FEFFFFD(2146435069) _freelist underflow threshold 2147483646");
                            entry.next = StartOfFreeList - dictionary._freeList;

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TKey>())
                            {
                                entry.key = default!;
                            }

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TValue>())
                            {
                                entry.value = default!;
                            }

                            dictionary._freeList = i;
                            dictionary._freeCount++;
                            return true;
                        }

                        last = i;
                        i = entry.next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop; which means a concurrent update has happened.
                            // Break out of the loop and throw, rather than looping forever.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                    }
                }

                actualKey = default;
                value = default;
                return false;
            }

            /// <summary>Attempts to add the specified key and value to the dictionary.</summary>
            /// <param name="key">The alternate key of the element to add.</param>
            /// <param name="value">The value of the element to add.</param>
            /// <returns>true if the key/value pair was added to the dictionary successfully; otherwise, false.</returns>
            /// <exception cref="ArgumentNullException"><paramref name="key"/> is <see langword="null"/>.</exception>
            public bool TryAdd(TAlternateKey key, TValue value)
            {
                ref TValue? slot = ref GetValueRefOrAddDefault(key, out bool exists);
                if (!exists)
                {
                    slot = value;
                    return true;
                }

                return false;
            }

            /// <inheritdoc cref="CollectionsMarshal.GetValueRefOrAddDefault{TKey, TValue}(Dictionary{TKey, TValue}, TKey, out bool)"/>
            internal ref TValue? GetValueRefOrAddDefault(TAlternateKey key, out bool exists)
            {
                // NOTE: this method is a mirror of GetValueRefOrAddDefault above. Keep it in sync.

                Dictionary<TKey, TValue> dictionary = Dictionary;
                IAlternateEqualityComparer<TAlternateKey, TKey> comparer = GetAlternateComparer(dictionary);

                if (dictionary._buckets == null)
                {
                    dictionary.Initialize(0);
                }
                Debug.Assert(dictionary._buckets != null);

                Entry[]? entries = dictionary._entries;
                Debug.Assert(entries != null, "expected entries to be non-null");

                uint hashCode = (uint)comparer.GetHashCode(key);

                uint collisionCount = 0;
                ref int bucket = ref dictionary.GetBucket(hashCode);
                int i = bucket - 1; // Value in _buckets is 1-based

                Debug.Assert(comparer is not null);
                while ((uint)i < (uint)entries.Length)
                {
                    if (entries[i].hashCode == hashCode && comparer.Equals(key, entries[i].key))
                    {
                        exists = true;

                        return ref entries[i].value!;
                    }

                    i = entries[i].next;

                    collisionCount++;
                    if (collisionCount > (uint)entries.Length)
                    {
                        // The chain of entries forms a loop; which means a concurrent update has happened.
                        // Break out of the loop and throw, rather than looping forever.
                        ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                    }
                }

                TKey actualKey = comparer.Create(key);
                if (actualKey is null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
                }

                int index;
                if (dictionary._freeCount > 0)
                {
                    index = dictionary._freeList;
                    Debug.Assert((StartOfFreeList - entries[dictionary._freeList].next) >= -1, "shouldn't overflow because `next` cannot underflow");
                    dictionary._freeList = StartOfFreeList - entries[dictionary._freeList].next;
                    dictionary._freeCount--;
                }
                else
                {
                    int count = dictionary._count;
                    if (count == entries.Length)
                    {
                        dictionary.Resize();
                        bucket = ref dictionary.GetBucket(hashCode);
                    }
                    index = count;
                    dictionary._count = count + 1;
                    entries = dictionary._entries;
                }

                ref Entry entry = ref entries![index];
                entry.hashCode = hashCode;
                entry.next = bucket - 1; // Value in _buckets is 1-based
                entry.key = actualKey;
                entry.value = default!;
                bucket = index + 1; // Value in _buckets is 1-based
                dictionary._version++;

                // Value types never rehash
                if (!typeof(TKey).IsValueType && collisionCount > HashHelpers.HashCollisionThreshold && comparer is NonRandomizedStringEqualityComparer)
                {
                    // If we hit the collision threshold we'll need to switch to the comparer which is using randomized string hashing
                    // i.e. EqualityComparer<string>.Default.
                    dictionary.Resize(entries.Length, true);

                    exists = false;

                    // At this point the entries array has been resized, so the current reference we have is no longer valid.
                    // We're forced to do a new lookup and return an updated reference to the new entry instance. This new
                    // lookup is guaranteed to always find a value though and it will never return a null reference here.
                    ref TValue? value = ref dictionary.FindValue(actualKey)!;

                    Debug.Assert(!Unsafe.IsNullRef(ref value), "the lookup result cannot be a null ref here");

                    return ref value;
                }

                exists = false;

                return ref entry.value!;
            }
        }

        /// <summary>
        /// A helper class containing APIs exposed through <see cref="CollectionsMarshal"/> or <see cref="CollectionExtensions"/>.
        /// These methods are relatively niche and only used in specific scenarios, so adding them in a separate type avoids
        /// the additional overhead on each <see cref="Dictionary{TKey, TValue}"/> instantiation, especially in AOT scenarios.
        /// </summary>
        internal static class CollectionsMarshalHelper
        {
            /// <inheritdoc cref="CollectionsMarshal.GetValueRefOrAddDefault{TKey, TValue}(Dictionary{TKey, TValue}, TKey, out bool)"/>
            public static ref TValue? GetValueRefOrAddDefault(Dictionary<TKey, TValue> dictionary, TKey key, out bool exists)
            {
                // NOTE: this method is mirrored by Dictionary<TKey, TValue>.TryInsert above.
                // If you make any changes here, make sure to keep that version in sync as well.

                if (key == null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
                }

                if (dictionary._buckets == null)
                {
                    dictionary.Initialize(0);
                }
                Debug.Assert(dictionary._buckets != null);

                Entry[]? entries = dictionary._entries;
                Debug.Assert(entries != null, "expected entries to be non-null");

                IEqualityComparer<TKey>? comparer = dictionary._comparer;
                Debug.Assert(comparer is not null || typeof(TKey).IsValueType);
                uint hashCode = (uint)((typeof(TKey).IsValueType && comparer == null) ? key.GetHashCode() : comparer!.GetHashCode(key));

                uint collisionCount = 0;
                ref int bucket = ref dictionary.GetBucket(hashCode);
                int i = bucket - 1; // Value in _buckets is 1-based

                if (typeof(TKey).IsValueType && // comparer can only be null for value types; enable JIT to eliminate entire if block for ref types
                    comparer == null)
                {
                    // ValueType: Devirtualize with EqualityComparer<TKey>.Default intrinsic
                    while ((uint)i < (uint)entries.Length)
                    {
                        if (entries[i].hashCode == hashCode && EqualityComparer<TKey>.Default.Equals(entries[i].key, key))
                        {
                            exists = true;

                            return ref entries[i].value!;
                        }

                        i = entries[i].next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop; which means a concurrent update has happened.
                            // Break out of the loop and throw, rather than looping forever.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                    }
                }
                else
                {
                    Debug.Assert(comparer is not null);
                    while ((uint)i < (uint)entries.Length)
                    {
                        if (entries[i].hashCode == hashCode && comparer.Equals(entries[i].key, key))
                        {
                            exists = true;

                            return ref entries[i].value!;
                        }

                        i = entries[i].next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop; which means a concurrent update has happened.
                            // Break out of the loop and throw, rather than looping forever.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                    }
                }

                int index;
                if (dictionary._freeCount > 0)
                {
                    index = dictionary._freeList;
                    Debug.Assert((StartOfFreeList - entries[dictionary._freeList].next) >= -1, "shouldn't overflow because `next` cannot underflow");
                    dictionary._freeList = StartOfFreeList - entries[dictionary._freeList].next;
                    dictionary._freeCount--;
                }
                else
                {
                    int count = dictionary._count;
                    if (count == entries.Length)
                    {
                        dictionary.Resize();
                        bucket = ref dictionary.GetBucket(hashCode);
                    }
                    index = count;
                    dictionary._count = count + 1;
                    entries = dictionary._entries;
                }

                ref Entry entry = ref entries![index];
                entry.hashCode = hashCode;
                entry.next = bucket - 1; // Value in _buckets is 1-based
                entry.key = key;
                entry.value = default!;
                bucket = index + 1; // Value in _buckets is 1-based
                dictionary._version++;

                // Value types never rehash
                if (!typeof(TKey).IsValueType && collisionCount > HashHelpers.HashCollisionThreshold && comparer is NonRandomizedStringEqualityComparer)
                {
                    // If we hit the collision threshold we'll need to switch to the comparer which is using randomized string hashing
                    // i.e. EqualityComparer<string>.Default.
                    dictionary.Resize(entries.Length, true);

                    exists = false;

                    // At this point the entries array has been resized, so the current reference we have is no longer valid.
                    // We're forced to do a new lookup and return an updated reference to the new entry instance. This new
                    // lookup is guaranteed to always find a value though and it will never return a null reference here.
                    ref TValue? value = ref dictionary.FindValue(key)!;

                    Debug.Assert(!Unsafe.IsNullRef(ref value), "the lookup result cannot be a null ref here");

                    return ref value;
                }

                exists = false;

                return ref entry.value!;
            }
        }

        public virtual void OnDeserialization(object? sender)
        {
            HashHelpers.SerializationInfoTable.TryGetValue(this, out SerializationInfo? siInfo);

            if (siInfo == null)
            {
                // We can return immediately if this function is called twice.
                // Note we remove the serialization info from the table at the end of this method.
                return;
            }

            int realVersion = siInfo.GetInt32(VersionName);
            int hashsize = siInfo.GetInt32(HashSizeName);
            _comparer = (IEqualityComparer<TKey>)siInfo.GetValue(ComparerName, typeof(IEqualityComparer<TKey>))!; // When serialized if comparer is null, we use the default.

            if (hashsize != 0)
            {
                Initialize(hashsize);

                KeyValuePair<TKey, TValue>[]? array = (KeyValuePair<TKey, TValue>[]?)
                    siInfo.GetValue(KeyValuePairsName, typeof(KeyValuePair<TKey, TValue>[]));

                if (array == null)
                {
                    ThrowHelper.ThrowSerializationException(ExceptionResource.Serialization_MissingKeys);
                }

                for (int i = 0; i < array.Length; i++)
                {
                    if (array[i].Key == null)
                    {
                        ThrowHelper.ThrowSerializationException(ExceptionResource.Serialization_NullKey);
                    }

                    Add(array[i].Key, array[i].Value);
                }
            }
            else
            {
                _buckets = null;
            }

            _version = realVersion;
            HashHelpers.SerializationInfoTable.Remove(this);
        }

        [Requires("0 < @this.SpecCapacity && @this.SpecCapacity <= @this.SpecSlots && @this.SpecSlots < 0x7FFFFFC3")]
        [Ensures("@this.SpecCapacity > Old(@this.SpecSlots) && @this.SpecSlots == Old(@this.SpecSlots) && @this.SpecCount == Old(@this.SpecCount)")]
        [Ensures("@this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecVersion == Old(@this.SpecVersion) && @this.SpecComparer == Old(@this.SpecComparer)")]
        private void Resize() => Resize(HashHelpers.ExpandPrime(_count), false);

        [Requires("Pal.Implies(forceNewHashCodes, !typeof(TKey).IsValueType && Dictionary<TKey, TValue>.NonRandomized(@this.SpecComparer))")]
        [Requires("0 < @this.SpecCapacity && @this.SpecCapacity <= newSize && newSize <= 0x7FFFFFC7 && System.Collections.HashHelpers.PrimeSize(newSize)")]
        [Ensures("@this.SpecCapacity == newSize && @this.SpecSlots == Old(@this.SpecSlots) && @this.SpecCount == Old(@this.SpecCount)")]
        [Ensures("@this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecVersion == Old(@this.SpecVersion)")]
        [Ensures("Pal.Implies(!forceNewHashCodes, @this.SpecComparer == Old(@this.SpecComparer))")]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        private void Resize(int newSize, bool forceNewHashCodes)
        {
            // Value types never rehash
            Debug.Assert(!forceNewHashCodes || !typeof(TKey).IsValueType);
            Debug.Assert(_entries != null, "_entries should be non-null");
            Debug.Assert(HashHelpers.IsPrime(newSize));
            Debug.Assert(newSize >= _entries.Length);

            Entry[] entries = new Entry[newSize];

            int count = _count;
            Ghost<Seq<Entry>> old0 = Pal.Contents(_entries);
            Array.Copy(_entries, entries, count);
            CopyOk(Pal.Contents(_buckets), old0.Value, Pal.Contents(entries), count, _freeList, _freeCount, _comparer);

            if (!typeof(TKey).IsValueType && forceNewHashCodes)
            {
                Debug.Assert(_comparer is NonRandomizedStringEqualityComparer);
                RandomizedSame(_comparer);
                PreFreeOf(Pal.Contents(entries), count, _freeList, _freeCount, _comparer);
                Ghost<Seq<Entry>> copied = Pal.Contents(entries);
                IEqualityComparer<TKey> comparer = _comparer = (IEqualityComparer<TKey>)((NonRandomizedStringEqualityComparer)_comparer).GetRandomizedEqualityComparer();

                RehashStart(copied.Value, count, _comparer);
                for (int i = 0; i < count; i++)
                {
                    Pal.Invariant(0 <= i && entries.Length == newSize && Holds(_comparer, comparer));
                    Pal.Invariant(Dictionary<TKey, TValue>.Rehashed(copied.Value, Pal.Contents(entries), count, i, _comparer));
                    Ghost<Seq<Entry>> before = Pal.Contents(entries);
                    if (entries[i].next >= -1)
                    {
                        entries[i].hashCode = (uint)comparer.GetHashCode(entries[i].key);
                    }
                    RehashStep(copied.Value, before.Value, Pal.Contents(entries), count, i, _comparer);
                }
                RehashDone(copied.Value, Pal.Contents(entries), count, _freeList, _freeCount, _comparer);
            }

            // Assign member variables after both arrays allocated to guard against corruption from OOM if second fails
            _buckets = new int[newSize];
#if TARGET_64BIT
            _fastModMultiplier = HashHelpers.GetFastModMultiplier((uint)newSize);
#endif
            Ghost<Seq<Entry>> source = Pal.Contents(entries);
            RebuildStart(Pal.Contents(_buckets), source.Value, count);
            for (int i = 0; i < count; i++)
            {
                Pal.Invariant(_buckets != null && _buckets.Length == newSize && entries.Length == newSize);
                Pal.Invariant(Rebuilt(Pal.Contents(_buckets), source.Value, Pal.Contents(entries), count, i));
                Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
                if (entries[i].next >= -1)
                {
                    RebuildBucket(Pal.Contents(_buckets), source.Value, Pal.Contents(entries), count, i);
                    ref int bucket = ref GetBucket(entries[i].hashCode);
                    entries[i].next = bucket - 1; // Value in _buckets is 1-based
                    bucket = i + 1;
                }
                RebuildStep(buckets0.Value, Pal.Contents(_buckets), source.Value, entries0.Value, Pal.Contents(entries), count, i);
            }

            _entries = entries;
            RebuildDone(Pal.Contents(_buckets), source.Value, Pal.Contents(_entries), count, _freeList, _freeCount, _comparer);
        }

        [Throws(typeof(ArgumentNullException), "key == null")]
        [Ensures("Pal.Implies(Result, Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key) && Dictionary<TKey, TValue>.RemovedAny(Old(@this.SpecComparer), Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecKeys, @this.SpecValues, key) && @this.SpecCount == Old(@this.SpecCount) - 1)")]
        [Ensures("Pal.Implies(!Result, !Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key) && @this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecCount == Old(@this.SpecCount))")]
        [Ensures("@this.SpecComparer == Old(@this.SpecComparer)")]
        [Rlimit(4)]
        public bool Remove(TKey key)
        {
            // The overload Remove(TKey key, out TValue value) is a copy of this method with one additional
            // statement to copy the value for entry being removed into the output parameter.
            // Code has been intentionally duplicated for performance reasons.
            // If you make any changes here, make sure to keep that version in sync as well.

            if (key == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
            }

            if (_buckets != null)
            {
                Debug.Assert(_entries != null, "entries should be non-null");
                uint collisionCount = 0;

                IEqualityComparer<TKey>? comparer = _comparer;
                Debug.Assert(typeof(TKey).IsValueType || comparer is not null);
                uint hashCode = (uint)(typeof(TKey).IsValueType && comparer == null ? key.GetHashCode() : comparer!.GetHashCode(key));

                Ghost<Seq<TKey>> keys0 = KeysOf(Pal.Contents(_entries), _count);
                Ghost<Seq<TValue>> values0 = ValuesOf(Pal.Contents(_entries), _count);
                Ghost<int> live0 = _count - _freeCount;
                Ghost<int> length0 = _entries.Length; // the measure may not name a field the loop writes (F3)
                SearchLastStart(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, comparer, key);
                ref int bucket = ref GetBucket(hashCode);
                Entry[]? entries = _entries;
                int last = -1;
                int i = bucket - 1; // Value in buckets is 1-based

                if (typeof(TKey).IsValueType && // comparer can only be null for value types; enable JIT to eliminate entire if block for ref types
                    comparer == null)
                {
                    while ((uint)i < (uint)entries.Length)
                    {
                        Pal.Invariant(entries != null && _buckets != null && _comparer == comparer && _entries == entries);
                        Pal.Invariant(0 <= _freeCount && _freeCount <= _count && _count <= entries.Length && _buckets.Length == entries.Length);
                        Pal.Invariant(typeof(TKey).IsValueType || _comparer != null);
                        Pal.Invariant(collisionCount <= (uint)entries.Length);
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.SearchLast(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, key, i, collisionCount, last)));
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && _count - _freeCount == live0.Value));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && Dictionary<TKey, TValue>.Mem(_comparer, keys0.Value, key) && Dictionary<TKey, TValue>.RemovedAny(_comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key) && _count - _freeCount == live0.Value - 1));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer) && _freeCount <= _count));
                        Pal.Invariant(entries.Length == length0.Value && entries.Length <= Array.MaxLength);
                        Pal.Decreases(length0.Value - collisionCount);
                        Pal.Assert(0 <= length0.Value - collisionCount);
                        ref Entry entry = ref entries[i];

                        if (entry.hashCode == hashCode && EqualityComparer<TKey>.Default.Equals(entry.key, key))
                        {
                            SearchNext(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                            Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                            Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
                            if (last < 0)
                            {
                                bucket = entry.next + 1; // Value in buckets is 1-based
                            }
                            else
                            {
                                entries[last].next = entry.next;
                            }

                            Debug.Assert((StartOfFreeList - _freeList) < 0, "shouldn't underflow because max hashtable length is MaxPrimeArrayLength = 0x7FEFFFFD(2146435069) _freelist underflow threshold 2147483646");
                            entry.next = StartOfFreeList - _freeList;

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TKey>())
                            {
                                entry.key = default!;
                            }

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TValue>())
                            {
                                entry.value = default!;
                            }

                            RemoveOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                            RemovedForget(comparer, keys0.Value, values0.Value, KeysOf(Pal.Contents(entries), _count), ValuesOf(Pal.Contents(entries), _count), key, entries0.Value[i].value);
                            _freeList = i;
                            _freeCount++;
                            Pal.Assert(0 <= length0.Value - collisionCount);
                            return true;
                        }

                        SearchLastStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                        last = i;
                        i = entry.next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop; which means a concurrent update has happened.
                            // Break out of the loop and throw, rather than looping forever.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                        Pal.Assert(collisionCount <= (uint)entries.Length && 0 <= length0.Value - collisionCount);
                    }
                    SearchLastAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                    Pal.Assert(!Dictionary<TKey, TValue>.Mem(_comparer, keys0.Value, key) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(_entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(_entries), _count) == values0.Value && _count - _freeCount == live0.Value);
                }
                else
                {
                    Debug.Assert(comparer is not null);
                    while ((uint)i < (uint)entries.Length)
                    {
                        Pal.Invariant(entries != null && _buckets != null && _comparer == comparer && _entries == entries);
                        Pal.Invariant(0 <= _freeCount && _freeCount <= _count && _count <= entries.Length && _buckets.Length == entries.Length);
                        Pal.Invariant(typeof(TKey).IsValueType || _comparer != null);
                        Pal.Invariant(collisionCount <= (uint)entries.Length);
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.SearchLast(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, key, i, collisionCount, last)));
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && _count - _freeCount == live0.Value));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && Dictionary<TKey, TValue>.Mem(_comparer, keys0.Value, key) && Dictionary<TKey, TValue>.RemovedAny(_comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key) && _count - _freeCount == live0.Value - 1));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer) && _freeCount <= _count));
                        Pal.Invariant(entries.Length == length0.Value && entries.Length <= Array.MaxLength);
                        Pal.Decreases(length0.Value - collisionCount);
                        Pal.Assert(0 <= length0.Value - collisionCount);
                        ref Entry entry = ref entries[i];

                        if (entry.hashCode == hashCode && comparer.Equals(entry.key, key))
                        {
                            SearchNext(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                            Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                            Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
                            if (last < 0)
                            {
                                bucket = entry.next + 1; // Value in buckets is 1-based
                            }
                            else
                            {
                                entries[last].next = entry.next;
                            }

                            Debug.Assert((StartOfFreeList - _freeList) < 0, "shouldn't underflow because max hashtable length is MaxPrimeArrayLength = 0x7FEFFFFD(2146435069) _freelist underflow threshold 2147483646");
                            entry.next = StartOfFreeList - _freeList;

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TKey>())
                            {
                                entry.key = default!;
                            }

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TValue>())
                            {
                                entry.value = default!;
                            }

                            RemoveOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                            RemovedForget(comparer, keys0.Value, values0.Value, KeysOf(Pal.Contents(entries), _count), ValuesOf(Pal.Contents(entries), _count), key, entries0.Value[i].value);
                            _freeList = i;
                            _freeCount++;
                            Pal.Assert(0 <= length0.Value - collisionCount);
                            return true;
                        }

                        SearchLastStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                        last = i;
                        i = entry.next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop; which means a concurrent update has happened.
                            // Break out of the loop and throw, rather than looping forever.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                        Pal.Assert(collisionCount <= (uint)entries.Length && 0 <= length0.Value - collisionCount);
                    }
                    SearchLastAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                    Pal.Assert(!Dictionary<TKey, TValue>.Mem(_comparer, keys0.Value, key) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(_entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(_entries), _count) == values0.Value && _count - _freeCount == live0.Value);
                }
            }
            return false;
        }

        [Throws(typeof(ArgumentNullException), "key == null")]
        [Ensures("Pal.Implies(Result, Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key) && Dictionary<TKey, TValue>.RemovedAny(Old(@this.SpecComparer), Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecKeys, @this.SpecValues, key) && @this.SpecCount == Old(@this.SpecCount) - 1)")]
        [Ensures("Pal.Implies(!Result, !Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key) && @this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecCount == Old(@this.SpecCount))")]
        [Ensures("@this.SpecComparer == Old(@this.SpecComparer)")]
        [Rlimit(4)]
        public bool Remove(TKey key, [MaybeNullWhen(false)] out TValue value)
        {
            // This overload is a copy of the overload Remove(TKey key) with one additional
            // statement to copy the value for entry being removed into the output parameter.
            // Code has been intentionally duplicated for performance reasons.
            // If you make any changes here, make sure to keep the other overload in sync as well.

            if (key == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
            }

            if (_buckets != null)
            {
                Debug.Assert(_entries != null, "entries should be non-null");
                uint collisionCount = 0;

                IEqualityComparer<TKey>? comparer = _comparer;
                Debug.Assert(typeof(TKey).IsValueType || comparer is not null);
                uint hashCode = (uint)(typeof(TKey).IsValueType && comparer == null ? key.GetHashCode() : comparer!.GetHashCode(key));

                Ghost<Seq<TKey>> keys0 = KeysOf(Pal.Contents(_entries), _count);
                Ghost<Seq<TValue>> values0 = ValuesOf(Pal.Contents(_entries), _count);
                Ghost<int> live0 = _count - _freeCount;
                Ghost<int> length0 = _entries.Length; // the measure may not name a field the loop writes (F3)
                SearchLastStart(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, comparer, key);
                ref int bucket = ref GetBucket(hashCode);
                Entry[]? entries = _entries;
                int last = -1;
                int i = bucket - 1; // Value in buckets is 1-based

                if (typeof(TKey).IsValueType && // comparer can only be null for value types; enable JIT to eliminate entire if block for ref types
                    comparer == null)
                {
                    while ((uint)i < (uint)entries.Length)
                    {
                        Pal.Invariant(entries != null && _buckets != null && _comparer == comparer && _entries == entries);
                        Pal.Invariant(0 <= _freeCount && _freeCount <= _count && _count <= entries.Length && _buckets.Length == entries.Length);
                        Pal.Invariant(typeof(TKey).IsValueType || _comparer != null);
                        Pal.Invariant(collisionCount <= (uint)entries.Length);
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.SearchLast(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, key, i, collisionCount, last)));
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && _count - _freeCount == live0.Value));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && Dictionary<TKey, TValue>.Mem(_comparer, keys0.Value, key) && Dictionary<TKey, TValue>.RemovedAny(_comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key) && _count - _freeCount == live0.Value - 1));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer) && _freeCount <= _count));
                        Pal.Invariant(entries.Length == length0.Value && entries.Length <= Array.MaxLength);
                        Pal.Decreases(length0.Value - collisionCount);
                        Pal.Assert(0 <= length0.Value - collisionCount);
                        ref Entry entry = ref entries[i];

                        if (entry.hashCode == hashCode && EqualityComparer<TKey>.Default.Equals(entry.key, key))
                        {
                            SearchNext(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                            Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                            Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
                            if (last < 0)
                            {
                                bucket = entry.next + 1; // Value in buckets is 1-based
                            }
                            else
                            {
                                entries[last].next = entry.next;
                            }

                            value = entry.value;

                            Debug.Assert((StartOfFreeList - _freeList) < 0, "shouldn't underflow because max hashtable length is MaxPrimeArrayLength = 0x7FEFFFFD(2146435069) _freelist underflow threshold 2147483646");
                            entry.next = StartOfFreeList - _freeList;

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TKey>())
                            {
                                entry.key = default!;
                            }

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TValue>())
                            {
                                entry.value = default!;
                            }

                            RemoveOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                            RemovedForget(comparer, keys0.Value, values0.Value, KeysOf(Pal.Contents(entries), _count), ValuesOf(Pal.Contents(entries), _count), key, entries0.Value[i].value);
                            _freeList = i;
                            _freeCount++;
                            Pal.Assert(0 <= length0.Value - collisionCount);
                            return true;
                        }

                        SearchLastStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                        last = i;
                        i = entry.next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop; which means a concurrent update has happened.
                            // Break out of the loop and throw, rather than looping forever.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                        Pal.Assert(collisionCount <= (uint)entries.Length && 0 <= length0.Value - collisionCount);
                    }
                    SearchLastAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                    Pal.Assert(!Dictionary<TKey, TValue>.Mem(_comparer, keys0.Value, key) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(_entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(_entries), _count) == values0.Value && _count - _freeCount == live0.Value);
                }
                else
                {
                    Debug.Assert(comparer is not null);
                    while ((uint)i < (uint)entries.Length)
                    {
                        Pal.Invariant(entries != null && _buckets != null && _comparer == comparer && _entries == entries);
                        Pal.Invariant(0 <= _freeCount && _freeCount <= _count && _count <= entries.Length && _buckets.Length == entries.Length);
                        Pal.Invariant(typeof(TKey).IsValueType || _comparer != null);
                        Pal.Invariant(collisionCount <= (uint)entries.Length);
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.SearchLast(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, key, i, collisionCount, last)));
                        Pal.Invariant(Pal.Implies(!Pal.Returned(), Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count) == values0.Value && _count - _freeCount == live0.Value));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && Dictionary<TKey, TValue>.Mem(_comparer, keys0.Value, key) && Dictionary<TKey, TValue>.RemovedAny(_comparer, keys0.Value, values0.Value, Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), _count), Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), _count), key) && _count - _freeCount == live0.Value - 1));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Dictionary<TKey, TValue>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer) && _freeCount <= _count));
                        Pal.Invariant(entries.Length == length0.Value && entries.Length <= Array.MaxLength);
                        Pal.Decreases(length0.Value - collisionCount);
                        Pal.Assert(0 <= length0.Value - collisionCount);
                        ref Entry entry = ref entries[i];

                        if (entry.hashCode == hashCode && comparer.Equals(entry.key, key))
                        {
                            SearchNext(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                            Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                            Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
                            if (last < 0)
                            {
                                bucket = entry.next + 1; // Value in buckets is 1-based
                            }
                            else
                            {
                                entries[last].next = entry.next;
                            }

                            value = entry.value;

                            Debug.Assert((StartOfFreeList - _freeList) < 0, "shouldn't underflow because max hashtable length is MaxPrimeArrayLength = 0x7FEFFFFD(2146435069) _freelist underflow threshold 2147483646");
                            entry.next = StartOfFreeList - _freeList;

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TKey>())
                            {
                                entry.key = default!;
                            }

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<TValue>())
                            {
                                entry.value = default!;
                            }

                            RemoveOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                            RemovedForget(comparer, keys0.Value, values0.Value, KeysOf(Pal.Contents(entries), _count), ValuesOf(Pal.Contents(entries), _count), key, entries0.Value[i].value);
                            _freeList = i;
                            _freeCount++;
                            Pal.Assert(0 <= length0.Value - collisionCount);
                            return true;
                        }

                        SearchLastStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                        last = i;
                        i = entry.next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop; which means a concurrent update has happened.
                            // Break out of the loop and throw, rather than looping forever.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                        Pal.Assert(collisionCount <= (uint)entries.Length && 0 <= length0.Value - collisionCount);
                    }
                    SearchLastAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, key, i, collisionCount, last);
                    Pal.Assert(!Dictionary<TKey, TValue>.Mem(_comparer, keys0.Value, key) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(_entries), _count) == keys0.Value && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(_entries), _count) == values0.Value && _count - _freeCount == live0.Value);
                }
            }

            value = default;
            return false;
        }

        [Throws(typeof(ArgumentNullException), "key == null")]
        [Ensures("Result == Dictionary<TKey, TValue>.Mem(@this.SpecComparer, @this.SpecKeys, key)")]
        [Ensures("Pal.Implies(Result, Dictionary<TKey, TValue>.Maps(@this.SpecComparer, @this.SpecKeys, @this.SpecValues, key, value))")]
        public bool TryGetValue(TKey key, [MaybeNullWhen(false)] out TValue value)
        {
            ref TValue valRef = ref FindValue(key);
            if (!Unsafe.IsNullRef(ref valRef))
            {
                value = valRef;
                return true;
            }

            value = default;
            return false;
        }

        [Requires("@this.SpecSlots < 0x7FFFFFC3")]
        [Throws(typeof(ArgumentNullException), "key == null")]
        [Ensures("Result == !Dictionary<TKey, TValue>.Mem(Old(@this.SpecComparer), Old(@this.SpecKeys), key)")]
        [Ensures("Pal.Implies(Result, Dictionary<TKey, TValue>.Added(Old(@this.SpecKeys), Old(@this.SpecValues), @this.SpecKeys, @this.SpecValues, key, value) && @this.SpecCount == Old(@this.SpecCount) + 1)")]
        [Ensures("Pal.Implies(!Result, @this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecCount == Old(@this.SpecCount))")]
        [Ensures("Dictionary<TKey, TValue>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        public bool TryAdd(TKey key, TValue value) =>
            TryInsert(key, value, InsertionBehavior.None);

        [Ensures("!Result")]
        bool ICollection<KeyValuePair<TKey, TValue>>.IsReadOnly => false;

        [Requires("array != null && index >= 0")]
        [Throws(typeof(ArgumentException), "index > Pal.Contents(array).Length || Pal.Contents(array).Length - index < @this.SpecCount")]
        [Ensures("@this.SpecKeys == Pal.Old(@this.SpecKeys) && @this.SpecValues == Pal.Old(@this.SpecValues) && @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecVersion == Pal.Old(@this.SpecVersion)")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("@this.SpecKeys.Length == @this.SpecCount")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.SpecKeys.Length, Dictionary<TKey, TValue>.Pairs(@this.SpecKeys, @this.SpecValues))")]
        void ICollection<KeyValuePair<TKey, TValue>>.CopyTo(KeyValuePair<TKey, TValue>[] array, int index) =>
            CopyTo(array, index);

        void ICollection.CopyTo(Array array, int index)
        {
            if (array == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.array);
            }

            if (array.Rank != 1)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_RankMultiDimNotSupported);
            }

            if (array.GetLowerBound(0) != 0)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_NonZeroLowerBound);
            }

            if ((uint)index > (uint)array.Length)
            {
                ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
            }

            if (array.Length - index < Count)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_ArrayPlusOffTooSmall);
            }

            if (array is KeyValuePair<TKey, TValue>[] pairs)
            {
                CopyTo(pairs, index);
            }
            else if (array is DictionaryEntry[] dictEntryArray)
            {
                Entry[]? entries = _entries;
                for (int i = 0; i < _count; i++)
                {
                    if (entries![i].next >= -1)
                    {
                        dictEntryArray[index++] = new DictionaryEntry(entries[i].key, entries[i].value);
                    }
                }
            }
            else
            {
                object[]? objects = array as object[];
                if (objects == null)
                {
                    ThrowHelper.ThrowArgumentException_Argument_IncompatibleArrayType();
                }

                try
                {
                    int count = _count;
                    Entry[]? entries = _entries;
                    for (int i = 0; i < count; i++)
                    {
                        if (entries![i].next >= -1)
                        {
                            objects[index++] = new KeyValuePair<TKey, TValue>(entries[i].key, entries[i].value);
                        }
                    }
                }
                catch (ArrayTypeMismatchException)
                {
                    ThrowHelper.ThrowArgumentException_Argument_IncompatibleArrayType();
                }
            }
        }

        IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<KeyValuePair<TKey, TValue>>)this).GetEnumerator();

        /// <summary>
        /// Ensures that the dictionary can hold up to 'capacity' entries without any further expansion of its backing storage
        /// </summary>
        [Requires("capacity <= 0x7FFFFFC3")]
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("capacity <= Result && Result == @this.SpecCapacity")]
        [Ensures("@this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecCount == Old(@this.SpecCount) && @this.SpecComparer == Old(@this.SpecComparer)")]
        public int EnsureCapacity(int capacity)
        {
            if (capacity < 0)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.capacity);
            }

            int currentCapacity = _entries == null ? 0 : _entries.Length;
            if (currentCapacity >= capacity)
            {
                return currentCapacity;
            }

            _version++;

            if (_buckets == null)
            {
                return Initialize(capacity);
            }

            int newSize = HashHelpers.GetPrime(capacity);
            Resize(newSize, forceNewHashCodes: false);
            return newSize;
        }

        /// <summary>
        /// Sets the capacity of this dictionary to what it would be if it had been originally initialized with all its entries
        /// </summary>
        /// <remarks>
        /// This method can be used to minimize the memory overhead
        /// once it is known that no new elements will be added.
        ///
        /// To allocate minimum size storage array, execute the following statements:
        ///
        /// dictionary.Clear();
        /// dictionary.TrimExcess();
        /// </remarks>
        [Ensures("@this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecCount == Old(@this.SpecCount) && @this.SpecComparer == Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCapacity <= Old(@this.SpecCapacity)")]
        public void TrimExcess() => TrimExcess(Count);

        /// <summary>
        /// Sets the capacity of this dictionary to hold up 'capacity' entries without any further expansion of its backing storage
        /// </summary>
        /// <remarks>
        /// This method can be used to minimize the memory overhead
        /// once it is known that no new elements will be added.
        /// </remarks>
        /// <exception cref="ArgumentOutOfRangeException">Passed capacity is lower than entries count.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < @this.SpecCount")]
        [Ensures("@this.SpecKeys == Old(@this.SpecKeys) && @this.SpecValues == Old(@this.SpecValues) && @this.SpecCount == Old(@this.SpecCount) && @this.SpecComparer == Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCapacity <= Old(@this.SpecCapacity)")]
        public void TrimExcess(int capacity)
        {
            if (capacity < Count)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.capacity);
            }

            int newSize = HashHelpers.GetPrimeAtLeast(capacity);
            Entry[]? oldEntries = _entries;
            if (oldEntries is null || newSize >= oldEntries.Length)
            {
                return;
            }

            _version++;

            Debug.Assert(HashHelpers.IsPrime(newSize));
            Debug.Assert(newSize >= Count);

            int[] buckets = new int[newSize];
            Entry[] entries = new Entry[newSize];

            WfCompactable(Pal.Contents(_buckets), Pal.Contents(oldEntries), _count, _freeList, _freeCount, _comparer);
            // Assign member variables after both arrays allocated to guard against corruption from OOM if second fails
            _freeList = -1;
#if TARGET_64BIT
            _fastModMultiplier = HashHelpers.GetFastModMultiplier((uint)newSize);
#endif
            _buckets = buckets;
            _entries = entries;

            CopyEntries(oldEntries, _count);
        }

        // [Open] (R27.23): `TrimExcess` calls it with the new, empty arrays in place and the old
        // entries in hand, where the invariant does not hold.
        [Open]
        [Requires("@this._entries != null && @this._buckets != null && 0 <= count && count <= entries.Length && @this._freeList == -1")]
        [Requires("Pal.Contents(@this._entries).Length > 0 && Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length && Dictionary<TKey, TValue>.Zeros(Pal.Contents(@this._buckets))")]
        [Requires("Dictionary<TKey, TValue>.Compactable(Pal.Contents(entries), count, @this._comparer) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), count).Length <= Pal.Contents(@this._entries).Length")]
        [Ensures("@this._entries != null && @this._buckets != null && @this._freeList == -1 && @this._freeCount == 0")]
        [Ensures("Pal.Contents(@this._entries).Length == Old(Pal.Contents(@this._entries).Length) && Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length")]
        [Ensures("@this._comparer == Old(@this._comparer) && @this._version == Old(@this._version)")]
        [Ensures("Pal.Contents(entries) == Old(Pal.Contents(entries)) && Dictionary<TKey, TValue>.KeysOf(Pal.Contents(@this._entries), @this._count).Length == @this._count")]
        [Ensures("Dictionary<TKey, TValue>.Wf(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count, @this._freeList, @this._freeCount, @this._comparer)")]
        [Ensures("Dictionary<TKey, TValue>.KeysOf(Pal.Contents(@this._entries), @this._count) == Dictionary<TKey, TValue>.KeysOf(Pal.Contents(entries), count) && Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(@this._entries), @this._count) == Dictionary<TKey, TValue>.ValuesOf(Pal.Contents(entries), count)")]
        private void CopyEntries(Entry[] entries, int count)
        {
            Debug.Assert(_entries is not null);

            Entry[] newEntries = _entries;
            int newCount = 0;
            Ghost<int> length0 = newEntries.Length;
            CompactStart(Pal.Contents(_buckets), Pal.Contents(entries), Pal.Contents(newEntries), count, _comparer);
            for (int i = 0; i < count; i++)
            {
                Pal.Invariant(0 <= i && i <= count && newEntries.Length == length0.Value && _buckets != null && _buckets.Length == length0.Value);
                Pal.Invariant(Dictionary<TKey, TValue>.Compacted(Pal.Contents(_buckets), Pal.Contents(entries), Pal.Contents(newEntries), count, i, newCount, _comparer));
                Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                Ghost<Seq<Entry>> entries0 = Pal.Contents(newEntries);
                Ghost<int> m0 = newCount;
                uint hashCode = entries[i].hashCode;
                if (entries[i].next >= -1)
                {
                    CompactRoom(Pal.Contents(_buckets), Pal.Contents(entries), Pal.Contents(newEntries), count, i, newCount, _comparer);
                    ref Entry entry = ref newEntries[newCount];
                    entry = entries[i];
                    ref int bucket = ref GetBucket(hashCode);
                    entry.next = bucket - 1; // Value in _buckets is 1-based
                    bucket = newCount + 1;
                    newCount++;
                }
                CompactStep(buckets0.Value, Pal.Contents(_buckets), Pal.Contents(entries), entries0.Value, Pal.Contents(newEntries), count, i, m0.Value, newCount, _comparer);
            }

            CompactDone(Pal.Contents(_buckets), Pal.Contents(entries), Pal.Contents(newEntries), count, newCount, _comparer);
            _count = newCount;
            _freeCount = 0;
        }

        [Ensures("!Result")]
        bool ICollection.IsSynchronized => false;

        object ICollection.SyncRoot => this;

        [Ensures("!Result")]
        bool IDictionary.IsFixedSize => false;

        [Ensures("!Result")]
        bool IDictionary.IsReadOnly => false;

        ICollection IDictionary.Keys => Keys;

        ICollection IDictionary.Values => Values;

        object? IDictionary.this[object key]
        {
            get
            {
                if (IsCompatibleKey(key))
                {
                    ref TValue value = ref FindValue((TKey)key);
                    if (!Unsafe.IsNullRef(ref value))
                    {
                        return value;
                    }
                }

                return null;
            }
            set
            {
                if (key == null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
                }
                ThrowHelper.IfNullAndNullsAreIllegalThenThrow<TValue>(value, ExceptionArgument.value);

                try
                {
                    TKey tempKey = (TKey)key;
                    try
                    {
                        this[tempKey] = (TValue)value!;
                    }
                    catch (InvalidCastException)
                    {
                        ThrowHelper.ThrowWrongValueTypeArgumentException(value, typeof(TValue));
                    }
                }
                catch (InvalidCastException)
                {
                    ThrowHelper.ThrowWrongKeyTypeArgumentException(key, typeof(TKey));
                }
            }
        }

        private static bool IsCompatibleKey(object key)
        {
            if (key == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
            }
            return key is TKey;
        }

        void IDictionary.Add(object key, object? value)
        {
            if (key == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.key);
            }
            ThrowHelper.IfNullAndNullsAreIllegalThenThrow<TValue>(value, ExceptionArgument.value);

            try
            {
                TKey tempKey = (TKey)key;

                try
                {
                    Add(tempKey, (TValue)value!);
                }
                catch (InvalidCastException)
                {
                    ThrowHelper.ThrowWrongValueTypeArgumentException(value, typeof(TValue));
                }
            }
            catch (InvalidCastException)
            {
                ThrowHelper.ThrowWrongKeyTypeArgumentException(key, typeof(TKey));
            }
        }

        bool IDictionary.Contains(object key)
        {
            if (IsCompatibleKey(key))
            {
                return ContainsKey((TKey)key);
            }

            return false;
        }

        [Ensures("Pal.Exists((Dictionary<TKey, TValue>.Enumerator e) => Pal.Boxes(Result, e) && " +
            "ReferenceEquals(e._dictionary, @this) && e._version == @this.SpecVersion && e._index == 0 && e._getEnumeratorRetType == Dictionary<TKey, TValue>.Enumerator.DictEntry)")]
        IDictionaryEnumerator IDictionary.GetEnumerator() => new Enumerator(this, Enumerator.DictEntry);

        void IDictionary.Remove(object key)
        {
            if (IsCompatibleKey(key))
            {
                Remove((TKey)key);
            }
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private ref int GetBucket(uint hashCode)
        {
            int[] buckets = _buckets!;
#if TARGET_64BIT
            return ref buckets[HashHelpers.FastMod(hashCode, (uint)buckets.Length, _fastModMultiplier)];
#else
            return ref buckets[(uint)hashCode % buckets.Length];
#endif
        }

        private struct Entry
        {
            public uint hashCode;
            /// <summary>
            /// 0-based index of next entry in chain: -1 means end of chain
            /// also encodes whether this entry _itself_ is part of the free list by changing sign and subtracting 3,
            /// so -2 means end of free list, -3 means index 0 but on free list, -4 means index 1 but on free list, etc.
            /// </summary>
            public int next;
            public TKey key;     // Key of entry
            public TValue value; // Value of entry
        }

        public struct Enumerator : IEnumerator<KeyValuePair<TKey, TValue>>, IDictionaryEnumerator
        {
            private readonly Dictionary<TKey, TValue> _dictionary;
            private readonly int _version;
            private int _index;
            private KeyValuePair<TKey, TValue> _current;
            private readonly int _getEnumeratorRetType;  // What should Enumerator.Current return?

            internal const int DictEntry = 1;
            internal const int KeyValuePair = 2;

            [Ensures("ReferenceEquals(@this._dictionary, dictionary) && @this._version == dictionary.SpecVersion && @this._index == 0 && @this._getEnumeratorRetType == getEnumeratorRetType")]
            internal Enumerator(Dictionary<TKey, TValue> dictionary, int getEnumeratorRetType)
            {
                _dictionary = dictionary;
                _version = dictionary._version;
                _index = 0;
                _getEnumeratorRetType = getEnumeratorRetType;
                _current = default;
            }

            [Requires("0 <= @this._index && @this._index <= @this._dictionary.SpecSlots + 1")]
            [Throws(typeof(InvalidOperationException), "@this._version != @this._dictionary.SpecVersion")]
            [Ensures("@this._version == @this._dictionary.SpecVersion")]
            [Ensures("0 <= @this._index && @this._index <= @this._dictionary.SpecSlots + 1")]
            [Ensures("@this._dictionary.SpecPrefixes.Length == @this._dictionary.SpecSlots + 1")]
            [Ensures("Pal.Implies(Result, Pal.Old(@this._index) < @this._index && @this._index <= @this._dictionary.SpecSlots && " +
                "@this._dictionary.SpecPrefixes[@this._index] == Pal.Snoc(@this._dictionary.SpecPrefixes[Pal.Old(@this._index)], @this._current))")]
            [Ensures("Pal.Implies(!Result, @this._index == @this._dictionary.SpecSlots + 1)")]
            [Ensures("Pal.Implies(!Result && Pal.Old(@this._index) <= @this._dictionary.SpecSlots, " +
                "@this._dictionary.SpecPrefixes[@this._dictionary.SpecSlots] == @this._dictionary.SpecPrefixes[Pal.Old(@this._index)])")]
            public bool MoveNext()
            {
                if (_version != _dictionary._version)
                {
                    ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                }

                Ghost<int> index0 = _index;
                Ghost<Seq<KeyValuePair<TKey, TValue>>> before = EntryPairsOf(Pal.Contents(_dictionary._entries), Math.Min(_index, _dictionary._count));
                // Use unsigned comparison since we set index to dictionary.count+1 when the enumeration ends.
                // dictionary.count+1 could be negative if dictionary.count is int.MaxValue
                while ((uint)_index < (uint)_dictionary._count)
                {
                    Pal.Invariant(index0.Value <= _index && _index <= _dictionary._count + 1);
                    Pal.Invariant(Pal.Implies(index0.Value <= _dictionary._count, _index <= _dictionary._count));
                    Pal.Invariant(Pal.Implies(!Pal.Returned() && index0.Value <= _dictionary._count,
                        EntryPairsOf(Pal.Contents(_dictionary._entries), _index) == before.Value));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && index0.Value < _index &&
                        EntryPairsOf(Pal.Contents(_dictionary._entries), _index) == Pal.Snoc(before.Value, _current)));
                    Pal.Decreases(_dictionary._count - _index);
                    ref Entry entry = ref _dictionary._entries![_index++];
                    PairsStep(Pal.Contents(_dictionary._entries), _index - 1);

                    if (entry.next >= -1)
                    {
                        _current = new KeyValuePair<TKey, TValue>(entry.key, entry.value);
                        return true;
                    }
                }

                _index = _dictionary._count + 1;
                _current = default;
                return false;
            }

            [Ensures("Pal.Same(Result, @this._current)")]
            public KeyValuePair<TKey, TValue> Current => _current;

            [Ensures("true")]
            public void Dispose() { }

            [Throws(typeof(InvalidOperationException), "@this._index == 0 || @this._index == @this._dictionary.SpecSlots + 1")]
            [Ensures("Pal.Implies(@this._getEnumeratorRetType == Dictionary<TKey, TValue>.Enumerator.DictEntry, Pal.Boxes(Result, new System.Collections.DictionaryEntry(@this._current.Key, @this._current.Value)))")]
            [Ensures("Pal.Implies(@this._getEnumeratorRetType != Dictionary<TKey, TValue>.Enumerator.DictEntry, Pal.Boxes(Result, @this._current))")]
            object? IEnumerator.Current
            {
                get
                {
                    if (_index == 0 || (_index == _dictionary._count + 1))
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen();
                    }

                    if (_getEnumeratorRetType == DictEntry)
                    {
                        return new DictionaryEntry(_current.Key, _current.Value);
                    }

                    return new KeyValuePair<TKey, TValue>(_current.Key, _current.Value);
                }
            }

            [Throws(typeof(InvalidOperationException), "@this._version != @this._dictionary.SpecVersion")]
            [Ensures("@this._version == @this._dictionary.SpecVersion && @this._index == 0")]
            void IEnumerator.Reset()
            {
                if (_version != _dictionary._version)
                {
                    ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                }

                _index = 0;
                _current = default;
            }

            [Throws(typeof(InvalidOperationException), "@this._index == 0 || @this._index == @this._dictionary.SpecSlots + 1")]
            [Ensures("Pal.Boxes(Result.Key, @this._current.Key) && Pal.Boxes(Result.Value, @this._current.Value)")]
            DictionaryEntry IDictionaryEnumerator.Entry
            {
                get
                {
                    if (_index == 0 || (_index == _dictionary._count + 1))
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen();
                    }

                    return new DictionaryEntry(_current.Key, _current.Value);
                }
            }

            [Throws(typeof(InvalidOperationException), "@this._index == 0 || @this._index == @this._dictionary.SpecSlots + 1")]
            [Ensures("Pal.Boxes(Result, @this._current.Key)")]
            object IDictionaryEnumerator.Key
            {
                get
                {
                    if (_index == 0 || (_index == _dictionary._count + 1))
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen();
                    }

                    return _current.Key;
                }
            }

            [Throws(typeof(InvalidOperationException), "@this._index == 0 || @this._index == @this._dictionary.SpecSlots + 1")]
            [Ensures("Pal.Boxes(Result, @this._current.Value)")]
            object? IDictionaryEnumerator.Value
            {
                get
                {
                    if (_index == 0 || (_index == _dictionary._count + 1))
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen();
                    }

                    return _current.Value;
                }
            }
        }

        [DebuggerTypeProxy(typeof(DictionaryKeyCollectionDebugView<,>))]
        [DebuggerDisplay("Count = {Count}")]
        public sealed class KeyCollection : ICollection<TKey>, ICollection, IReadOnlyCollection<TKey>
        {
            private readonly Dictionary<TKey, TValue> _dictionary;

            [Ensures("ReferenceEquals(@this._dictionary, dictionary)")]
            public KeyCollection(Dictionary<TKey, TValue> dictionary)
            {
                if (dictionary == null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.dictionary);
                }

                _dictionary = dictionary;
            }

            [Ensures("ReferenceEquals(Result._dictionary, @this._dictionary) && Result._version == @this._dictionary.SpecVersion && Result._index == 0")]
            public Enumerator GetEnumerator() => new Enumerator(_dictionary);

            [Requires("array != null && index >= 0")]
            [Throws(typeof(ArgumentOutOfRangeException), "index > Pal.Contents(array).Length")]
            [Throws(typeof(ArgumentException), "index <= Pal.Contents(array).Length && Pal.Contents(array).Length - index < @this._dictionary.SpecCount")]
            [Ensures("@this._dictionary.SpecKeys == Pal.Old(@this._dictionary.SpecKeys) && @this._dictionary.SpecCount == Pal.Old(@this._dictionary.SpecCount) && @this._dictionary.SpecVersion == Pal.Old(@this._dictionary.SpecVersion)")]
            [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
            [Ensures("@this._dictionary.SpecKeys.Length == @this._dictionary.SpecCount")]
            [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this._dictionary.SpecKeys.Length, @this._dictionary.SpecKeys)")]
            [Rlimit(4)]
            public void CopyTo(TKey[] array, int index)
            {
                if (array == null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.array);
                }

                if (index < 0 || index > array.Length)
                {
                    ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
                }

                if (array.Length - index < _dictionary.Count)
                {
                    ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_ArrayPlusOffTooSmall);
                }

                PairsCount(Pal.Contents(_dictionary._buckets), Pal.Contents(_dictionary._entries), _dictionary._count, _dictionary._freeList, _dictionary._freeCount, _dictionary._comparer);
                int count = _dictionary._count;
                Entry[]? entries = _dictionary._entries;
                Ghost<Seq<TKey>> array0 = Pal.Contents(array);
                Ghost<int> index0 = index;
                KeysPrefix(Pal.Contents(entries), 0, count);
                for (int i = 0; i < count; i++)
                {
                    Pal.Invariant(0 <= i && i <= count && count == _dictionary._count && (entries != null || count == 0));
                    Pal.Invariant(index == index0.Value + KeysOf(Pal.Contents(entries), i).Length);
                    Pal.Invariant(index0.Value + KeysOf(Pal.Contents(entries), count).Length <= array0.Value.Length);
                    Pal.Invariant(Pal.Contents(array).Length == array0.Value.Length);
                    Pal.Invariant(Pal.Contents(array) == Pal.Splice(array0.Value, index0.Value, index, KeysOf(Pal.Contents(entries), i)));
                    Pal.Invariant(KeysOf(Pal.Contents(entries), i).Length <= KeysOf(Pal.Contents(entries), count).Length);
                    Pal.Invariant(KeysOf(Pal.Contents(entries), i) == Pal.Slice(KeysOf(Pal.Contents(entries), count), 0, KeysOf(Pal.Contents(entries), i).Length));
                    KeysStep(Pal.Contents(entries), i);
                    KeysPrefix(Pal.Contents(entries), i + 1, count);
                    if (entries![i].next >= -1) array[index++] = entries[i].key;
                }
            }

            [Ensures("Result == @this._dictionary.SpecCount")]
            public int Count => _dictionary.Count;

            [Ensures("Result")]
            bool ICollection<TKey>.IsReadOnly => true;

            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void ICollection<TKey>.Add(TKey item) =>
                ThrowHelper.ThrowNotSupportedException(ExceptionResource.NotSupported_KeyCollectionSet);

            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void ICollection<TKey>.Clear() =>
                ThrowHelper.ThrowNotSupportedException(ExceptionResource.NotSupported_KeyCollectionSet);

            [Throws(typeof(ArgumentNullException), "item == null")]
            [Ensures("Result == Dictionary<TKey, TValue>.Mem(@this._dictionary.SpecComparer, @this._dictionary.SpecKeys, item)")]
            public bool Contains(TKey item) =>
                _dictionary.ContainsKey(item);

            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            bool ICollection<TKey>.Remove(TKey item)
            {
                ThrowHelper.ThrowNotSupportedException(ExceptionResource.NotSupported_KeyCollectionSet);
                return false;
            }

            [Ensures("Pal.Implies(@this._dictionary.SpecCount != 0, Pal.Exists((Dictionary<TKey, TValue>.KeyCollection.Enumerator e) => Pal.Boxes(Result, e) && " +
                "ReferenceEquals(e._dictionary, @this._dictionary) && e._version == @this._dictionary.SpecVersion && e._index == 0))")]
            IEnumerator<TKey> IEnumerable<TKey>.GetEnumerator() =>
                Count == 0 ? SZGenericArrayEnumerator<TKey>.Empty :
                GetEnumerator();

            IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<TKey>)this).GetEnumerator();

            void ICollection.CopyTo(Array array, int index)
            {
                if (array == null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.array);
                }

                if (array.Rank != 1)
                {
                    ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_RankMultiDimNotSupported);
                }

                if (array.GetLowerBound(0) != 0)
                {
                    ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_NonZeroLowerBound);
                }

                if ((uint)index > (uint)array.Length)
                {
                    ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
                }

                if (array.Length - index < _dictionary.Count)
                {
                    ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_ArrayPlusOffTooSmall);
                }

                if (array is TKey[] keys)
                {
                    CopyTo(keys, index);
                }
                else
                {
                    object[]? objects = array as object[];
                    if (objects == null)
                    {
                        ThrowHelper.ThrowArgumentException_Argument_IncompatibleArrayType();
                    }

                    int count = _dictionary._count;
                    Entry[]? entries = _dictionary._entries;
                    try
                    {
                        for (int i = 0; i < count; i++)
                        {
                            if (entries![i].next >= -1) objects[index++] = entries[i].key;
                        }
                    }
                    catch (ArrayTypeMismatchException)
                    {
                        ThrowHelper.ThrowArgumentException_Argument_IncompatibleArrayType();
                    }
                }
            }

            [Ensures("!Result")]
            bool ICollection.IsSynchronized => false;

            object ICollection.SyncRoot => ((ICollection)_dictionary).SyncRoot;

            public struct Enumerator : IEnumerator<TKey>, IEnumerator
            {
                private readonly Dictionary<TKey, TValue> _dictionary;
                private int _index;
                private readonly int _version;
                private TKey? _currentKey;

                [Ensures("ReferenceEquals(@this._dictionary, dictionary) && @this._version == dictionary.SpecVersion && @this._index == 0")]
                internal Enumerator(Dictionary<TKey, TValue> dictionary)
                {
                    _dictionary = dictionary;
                    _version = dictionary._version;
                    _index = 0;
                    _currentKey = default;
                }

                [Ensures("true")]
                public void Dispose() { }

                [Requires("0 <= @this._index && @this._index <= @this._dictionary.SpecSlots + 1")]
                [Throws(typeof(InvalidOperationException), "@this._version != @this._dictionary.SpecVersion")]
                [Ensures("@this._version == @this._dictionary.SpecVersion")]
                [Ensures("0 <= @this._index && @this._index <= @this._dictionary.SpecSlots + 1")]
                [Ensures("@this._dictionary.SpecPrefixes.Length == @this._dictionary.SpecSlots + 1")]
                [Ensures("Pal.Implies(Result, Pal.Old(@this._index) < @this._index && @this._index <= @this._dictionary.SpecSlots && " +
                    "Dictionary<TKey, TValue>.Firsts(@this._dictionary.SpecPrefixes[@this._index]) == Pal.Snoc(Dictionary<TKey, TValue>.Firsts(@this._dictionary.SpecPrefixes[Pal.Old(@this._index)]), @this._currentKey))")]
                [Ensures("Pal.Implies(!Result, @this._index == @this._dictionary.SpecSlots + 1)")]
                [Ensures("Pal.Implies(!Result && Pal.Old(@this._index) <= @this._dictionary.SpecSlots, " +
                    "@this._dictionary.SpecPrefixes[@this._dictionary.SpecSlots] == @this._dictionary.SpecPrefixes[Pal.Old(@this._index)])")]
                public bool MoveNext()
                {
                    if (_version != _dictionary._version)
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                    }

                    Ghost<int> index0 = _index;
                    Ghost<Seq<KeyValuePair<TKey, TValue>>> before = EntryPairsOf(Pal.Contents(_dictionary._entries), Math.Min(_index, _dictionary._count));
                    while ((uint)_index < (uint)_dictionary._count)
                    {
                        Pal.Invariant(index0.Value <= _index && _index <= _dictionary._count + 1);
                        Pal.Invariant(Pal.Implies(index0.Value <= _dictionary._count, _index <= _dictionary._count));
                        Pal.Invariant(Pal.Implies(!Pal.Returned() && index0.Value <= _dictionary._count,
                            EntryPairsOf(Pal.Contents(_dictionary._entries), _index) == before.Value));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && index0.Value < _index &&
                            Firsts(EntryPairsOf(Pal.Contents(_dictionary._entries), _index)) == Pal.Snoc(Firsts(before.Value), _currentKey)));
                        Pal.Decreases(_dictionary._count - _index);
                        ref Entry entry = ref _dictionary._entries![_index++];
                        PairsStep(Pal.Contents(_dictionary._entries), _index - 1);

                        if (entry.next >= -1)
                        {
                            _currentKey = entry.key;
                            return true;
                        }
                    }

                    _index = _dictionary._count + 1;
                    _currentKey = default;
                    return false;
                }

                [Ensures("Pal.Same(Result, @this._currentKey)")]
                public TKey Current => _currentKey!;

                [Throws(typeof(InvalidOperationException), "@this._index == 0 || @this._index == @this._dictionary.SpecSlots + 1")]
                [Ensures("Pal.Boxes(Result, @this._currentKey)")]
                object? IEnumerator.Current
                {
                    get
                    {
                        if (_index == 0 || (_index == _dictionary._count + 1))
                        {
                            ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen();
                        }

                        return _currentKey;
                    }
                }

                [Throws(typeof(InvalidOperationException), "@this._version != @this._dictionary.SpecVersion")]
                [Ensures("@this._version == @this._dictionary.SpecVersion && @this._index == 0")]
                void IEnumerator.Reset()
                {
                    if (_version != _dictionary._version)
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                    }

                    _index = 0;
                    _currentKey = default;
                }
            }
        }

        [DebuggerTypeProxy(typeof(DictionaryValueCollectionDebugView<,>))]
        [DebuggerDisplay("Count = {Count}")]
        public sealed class ValueCollection : ICollection<TValue>, ICollection, IReadOnlyCollection<TValue>
        {
            private readonly Dictionary<TKey, TValue> _dictionary;

            [Ensures("ReferenceEquals(@this._dictionary, dictionary)")]
            public ValueCollection(Dictionary<TKey, TValue> dictionary)
            {
                if (dictionary == null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.dictionary);
                }

                _dictionary = dictionary;
            }

            [Ensures("ReferenceEquals(Result._dictionary, @this._dictionary) && Result._version == @this._dictionary.SpecVersion && Result._index == 0")]
            public Enumerator GetEnumerator() => new Enumerator(_dictionary);

            [Requires("array != null && index >= 0")]
            [Throws(typeof(ArgumentOutOfRangeException), "index > Pal.Contents(array).Length")]
            [Throws(typeof(ArgumentException), "index <= Pal.Contents(array).Length && Pal.Contents(array).Length - index < @this._dictionary.SpecCount")]
            [Ensures("@this._dictionary.SpecValues == Pal.Old(@this._dictionary.SpecValues) && @this._dictionary.SpecCount == Pal.Old(@this._dictionary.SpecCount) && @this._dictionary.SpecVersion == Pal.Old(@this._dictionary.SpecVersion)")]
            [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
            [Ensures("@this._dictionary.SpecValues.Length == @this._dictionary.SpecCount")]
            [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this._dictionary.SpecValues.Length, @this._dictionary.SpecValues)")]
            [Rlimit(4)]
            public void CopyTo(TValue[] array, int index)
            {
                if (array == null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.array);
                }

                if ((uint)index > array.Length)
                {
                    ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
                }

                if (array.Length - index < _dictionary.Count)
                {
                    ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_ArrayPlusOffTooSmall);
                }

                PairsCount(Pal.Contents(_dictionary._buckets), Pal.Contents(_dictionary._entries), _dictionary._count, _dictionary._freeList, _dictionary._freeCount, _dictionary._comparer);
                int count = _dictionary._count;
                Entry[]? entries = _dictionary._entries;
                Ghost<Seq<TValue>> array0 = Pal.Contents(array);
                Ghost<int> index0 = index;
                ValuesPrefix(Pal.Contents(entries), 0, count);
                for (int i = 0; i < count; i++)
                {
                    Pal.Invariant(0 <= i && i <= count && count == _dictionary._count && (entries != null || count == 0));
                    Pal.Invariant(index == index0.Value + ValuesOf(Pal.Contents(entries), i).Length);
                    Pal.Invariant(index0.Value + ValuesOf(Pal.Contents(entries), count).Length <= array0.Value.Length);
                    Pal.Invariant(Pal.Contents(array).Length == array0.Value.Length);
                    Pal.Invariant(Pal.Contents(array) == Pal.Splice(array0.Value, index0.Value, index, ValuesOf(Pal.Contents(entries), i)));
                    Pal.Invariant(ValuesOf(Pal.Contents(entries), i).Length <= ValuesOf(Pal.Contents(entries), count).Length);
                    Pal.Invariant(ValuesOf(Pal.Contents(entries), i) == Pal.Slice(ValuesOf(Pal.Contents(entries), count), 0, ValuesOf(Pal.Contents(entries), i).Length));
                    ValuesStep(Pal.Contents(entries), i);
                    ValuesPrefix(Pal.Contents(entries), i + 1, count);
                    if (entries![i].next >= -1) array[index++] = entries[i].value;
                }
            }

            [Ensures("Result == @this._dictionary.SpecCount")]
            public int Count => _dictionary.Count;

            [Ensures("Result")]
            bool ICollection<TValue>.IsReadOnly => true;

            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void ICollection<TValue>.Add(TValue item) =>
                ThrowHelper.ThrowNotSupportedException(ExceptionResource.NotSupported_ValueCollectionSet);

            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            bool ICollection<TValue>.Remove(TValue item)
            {
                ThrowHelper.ThrowNotSupportedException(ExceptionResource.NotSupported_ValueCollectionSet);
                return false;
            }

            [Throws(typeof(NotSupportedException))]
            [Ensures("false")]
            void ICollection<TValue>.Clear() =>
                ThrowHelper.ThrowNotSupportedException(ExceptionResource.NotSupported_ValueCollectionSet);

            [Ensures("Result == Dictionary<TKey, TValue>.HasValue(@this._dictionary.SpecValues, item)")]
            bool ICollection<TValue>.Contains(TValue item) => _dictionary.ContainsValue(item);

            [Ensures("Pal.Implies(@this._dictionary.SpecCount != 0, Pal.Exists((Dictionary<TKey, TValue>.ValueCollection.Enumerator e) => Pal.Boxes(Result, e) && " +
                "ReferenceEquals(e._dictionary, @this._dictionary) && e._version == @this._dictionary.SpecVersion && e._index == 0))")]
            IEnumerator<TValue> IEnumerable<TValue>.GetEnumerator() =>
                Count == 0 ? SZGenericArrayEnumerator<TValue>.Empty :
                GetEnumerator();

            IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<TValue>)this).GetEnumerator();

            void ICollection.CopyTo(Array array, int index)
            {
                if (array == null)
                {
                    ThrowHelper.ThrowArgumentNullException(ExceptionArgument.array);
                }

                if (array.Rank != 1)
                {
                    ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_RankMultiDimNotSupported);
                }

                if (array.GetLowerBound(0) != 0)
                {
                    ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_NonZeroLowerBound);
                }

                if ((uint)index > (uint)array.Length)
                {
                    ThrowHelper.ThrowIndexArgumentOutOfRange_NeedNonNegNumException();
                }

                if (array.Length - index < _dictionary.Count)
                {
                    ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_ArrayPlusOffTooSmall);
                }

                if (array is TValue[] values)
                {
                    CopyTo(values, index);
                }
                else
                {
                    object[]? objects = array as object[];
                    if (objects == null)
                    {
                        ThrowHelper.ThrowArgumentException_Argument_IncompatibleArrayType();
                    }

                    int count = _dictionary._count;
                    Entry[]? entries = _dictionary._entries;
                    try
                    {
                        for (int i = 0; i < count; i++)
                        {
                            if (entries![i].next >= -1) objects[index++] = entries[i].value!;
                        }
                    }
                    catch (ArrayTypeMismatchException)
                    {
                        ThrowHelper.ThrowArgumentException_Argument_IncompatibleArrayType();
                    }
                }
            }

            [Ensures("!Result")]
            bool ICollection.IsSynchronized => false;

            object ICollection.SyncRoot => ((ICollection)_dictionary).SyncRoot;

            public struct Enumerator : IEnumerator<TValue>, IEnumerator
            {
                private readonly Dictionary<TKey, TValue> _dictionary;
                private int _index;
                private readonly int _version;
                private TValue? _currentValue;

                [Ensures("ReferenceEquals(@this._dictionary, dictionary) && @this._version == dictionary.SpecVersion && @this._index == 0")]
                internal Enumerator(Dictionary<TKey, TValue> dictionary)
                {
                    _dictionary = dictionary;
                    _version = dictionary._version;
                    _index = 0;
                    _currentValue = default;
                }

                [Ensures("true")]
                public void Dispose() { }

                [Requires("0 <= @this._index && @this._index <= @this._dictionary.SpecSlots + 1")]
                [Throws(typeof(InvalidOperationException), "@this._version != @this._dictionary.SpecVersion")]
                [Ensures("@this._version == @this._dictionary.SpecVersion")]
                [Ensures("0 <= @this._index && @this._index <= @this._dictionary.SpecSlots + 1")]
                [Ensures("@this._dictionary.SpecPrefixes.Length == @this._dictionary.SpecSlots + 1")]
                [Ensures("Pal.Implies(Result, Pal.Old(@this._index) < @this._index && @this._index <= @this._dictionary.SpecSlots && " +
                    "Dictionary<TKey, TValue>.Seconds(@this._dictionary.SpecPrefixes[@this._index]) == Pal.Snoc(Dictionary<TKey, TValue>.Seconds(@this._dictionary.SpecPrefixes[Pal.Old(@this._index)]), @this._currentValue))")]
                [Ensures("Pal.Implies(!Result, @this._index == @this._dictionary.SpecSlots + 1)")]
                [Ensures("Pal.Implies(!Result && Pal.Old(@this._index) <= @this._dictionary.SpecSlots, " +
                    "@this._dictionary.SpecPrefixes[@this._dictionary.SpecSlots] == @this._dictionary.SpecPrefixes[Pal.Old(@this._index)])")]
                public bool MoveNext()
                {
                    if (_version != _dictionary._version)
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                    }

                    Ghost<int> index0 = _index;
                    Ghost<Seq<KeyValuePair<TKey, TValue>>> before = EntryPairsOf(Pal.Contents(_dictionary._entries), Math.Min(_index, _dictionary._count));
                    while ((uint)_index < (uint)_dictionary._count)
                    {
                        Pal.Invariant(index0.Value <= _index && _index <= _dictionary._count + 1);
                        Pal.Invariant(Pal.Implies(index0.Value <= _dictionary._count, _index <= _dictionary._count));
                        Pal.Invariant(Pal.Implies(!Pal.Returned() && index0.Value <= _dictionary._count,
                            EntryPairsOf(Pal.Contents(_dictionary._entries), _index) == before.Value));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && index0.Value < _index &&
                            Seconds(EntryPairsOf(Pal.Contents(_dictionary._entries), _index)) == Pal.Snoc(Seconds(before.Value), _currentValue)));
                        Pal.Decreases(_dictionary._count - _index);
                        ref Entry entry = ref _dictionary._entries![_index++];
                        PairsStep(Pal.Contents(_dictionary._entries), _index - 1);

                        if (entry.next >= -1)
                        {
                            _currentValue = entry.value;
                            return true;
                        }
                    }
                    _index = _dictionary._count + 1;
                    _currentValue = default;
                    return false;
                }

                [Ensures("Pal.Same(Result, @this._currentValue)")]
                public TValue Current => _currentValue!;

                [Throws(typeof(InvalidOperationException), "@this._index == 0 || @this._index == @this._dictionary.SpecSlots + 1")]
                [Ensures("Pal.Boxes(Result, @this._currentValue)")]
                object? IEnumerator.Current
                {
                    get
                    {
                        if (_index == 0 || (_index == _dictionary._count + 1))
                        {
                            ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen();
                        }

                        return _currentValue;
                    }
                }

                [Throws(typeof(InvalidOperationException), "@this._version != @this._dictionary.SpecVersion")]
                [Ensures("@this._version == @this._dictionary.SpecVersion && @this._index == 0")]
                void IEnumerator.Reset()
                {
                    if (_version != _dictionary._version)
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                    }

                    _index = 0;
                    _currentValue = default;
                }
            }
        }
    }
}
