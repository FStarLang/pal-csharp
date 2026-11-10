// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.ComponentModel;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Serialization;
using PalLang;

namespace System.Collections.Generic
{
    /// <summary>The abstract state of a <see cref="HashSet{T}"/>.</summary>
    [Spec]
    public struct HashSetModel<T>
    {
        public SpecInt Count;
        /// <summary>The live elements, in entry order.</summary>
        public Seq<T> Items;
        /// <summary>The comparer the set was built with; null means the default comparer.</summary>
        public IEqualityComparer<T>? Comparer;
        /// <summary>The modification counter an enumerator checks.</summary>
        public SpecInt Version;
        /// <summary>The entries in use, live or free: an enumerator walks <c>[0, Slots)</c>.</summary>
        public SpecInt Slots;
        /// <summary><c>Prefixes[i]</c> is the live elements among the first <c>i</c> entries, for <c>0 &lt;= i &lt;= Slots</c>.</summary>
        public Seq<Seq<T>> Prefixes;
        /// <summary>The length of the entries array: how many elements fit without a resize.</summary>
        public SpecInt Capacity;
    }

    [DebuggerTypeProxy(typeof(ICollectionDebugView<>))]
    [DebuggerDisplay("Count = {Count}")]
    [Serializable]
    [TypeForwardedFrom("System.Core, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    [Invariant("0 <= _freeCount && _freeCount <= _count && _count <= _entries.Length")]
    [Invariant("(_buckets == null) == (_entries == null)")]
    [Invariant("_buckets.Length == _entries.Length")]
    [Invariant("_entries != null || _count == 0")]
    [Invariant("_entries != null || _entries.Length == 0")]
    [Invariant("_entries == null || _entries.Length > 0")]
    [Invariant("_entries == null || _entries.Length <= Array.MaxLength")]
    [Invariant("_entries == null || System.Collections.HashHelpers.PrimeSize(_entries.Length)")]
    [Invariant("typeof(T).IsValueType || _comparer != null")]
    [Invariant("_buckets == null || HashSet<T>.Wf(Contents(_buckets), Contents(_entries), _count, _freeList, _freeCount, _comparer)")]
    public class HashSet<T> : ICollection<T>, ISet<T>, IReadOnlyCollection<T>, IReadOnlySet<T>, ISerializable, IDeserializationCallback
    {
        // This uses the same array-based implementation as Dictionary<TKey, TValue>.

        // Constants for serialization
        private const string CapacityName = "Capacity"; // Do not rename (binary serialization)
        private const string ElementsName = "Elements"; // Do not rename (binary serialization)
        private const string ComparerName = "Comparer"; // Do not rename (binary serialization)
        private const string VersionName = "Version"; // Do not rename (binary serialization)

        /// <summary>Cutoff point for stackallocs. This corresponds to the number of ints.</summary>
        private const int StackAllocThreshold = 100;

        /// <summary>
        /// When constructing a hashset from an existing collection, it may contain duplicates,
        /// so this is used as the max acceptable excess ratio of capacity to count. Note that
        /// this is only used on the ctor and not to automatically shrink if the hashset has, e.g,
        /// a lot of adds followed by removes. Users must explicitly shrink by calling TrimExcess.
        /// This is set to 3 because capacity is acceptable as 2x rounded up to nearest prime.
        /// </summary>
        private const int ShrinkThreshold = 3;
        private const int StartOfFreeList = -3;

        private int[]? _buckets;
        private Entry[]? _entries;
#if TARGET_64BIT
        private ulong _fastModMultiplier;
#endif
        private int _count;
        private int _freeList;
        private int _freeCount;
        [Wrapping] private int _version;
        private IEqualityComparer<T>? _comparer;

        [Model]
        private HashSetModel<T> Model => new HashSetModel<T>
        {
            Count = _count - _freeCount,
            Items = ItemsOf(Pal.Contents(_entries), _count),
            Comparer = _comparer,
            Version = _version,
            Slots = _count,
            Prefixes = PrefixesOf(Pal.Contents(_entries), _count),
            Capacity = Pal.Contents(_entries).Length,
        };

        [Spec]
        public SpecInt SpecCapacity => Model.Capacity;

        /// <summary>The elements.</summary>
        [Spec]
        public Seq<T> SpecItems => Model.Items;

        /// <summary>The comparer the set was built with.</summary>
        [Spec]
        public IEqualityComparer<T>? SpecComparer => Model.Comparer;

        [Spec]
        public SpecInt SpecVersion => Model.Version;

        [Spec]
        public SpecInt SpecSlots => Model.Slots;

        [Spec]
        public Seq<Seq<T>> SpecPrefixes => Model.Prefixes;

        // The hash table's theory (pal/HashSet/HashSetChain.fst, Pulse.Lib.CSharp.HashChain).
        [Spec]
        [PulseBody("HashSetChain.wf $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        private static bool Wf(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("HashSetChain.items $(entries) $(count)")]
        private static Seq<T> ItemsOf(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= i && i < entries.Length")]
        [Ensures("Pal.Implies(entries[i].Next >= -1, HashSet<T>.ItemsOf(entries, i + 1) == Pal.Snoc(HashSet<T>.ItemsOf(entries, i), entries[i].Value))")]
        [Ensures("Pal.Implies(entries[i].Next < -1, HashSet<T>.ItemsOf(entries, i + 1) == HashSet<T>.ItemsOf(entries, i))")]
        [PulseBody("HashSetChain.items_step $(entries) $(i)")]
        [Conditional("PAL")]
        private static void ItemsStep(Seq<Entry> entries, SpecInt i) { }

        [Lemma]
        [Requires("0 <= freeCount && freeCount <= count && (count == 0 || HashSet<T>.Wf(buckets, entries, count, freeList, freeCount, comparer))")]
        [Ensures("HashSet<T>.ItemsOf(entries, count).Length == count - freeCount")]
        [PulseBody("HashSetChain.items_count $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void ItemsCount(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<T>? comparer) { }

        [Lemma]
        [Requires("0 <= i && i <= n && n <= entries.Length")]
        [Ensures("HashSet<T>.ItemsOf(entries, i).Length <= HashSet<T>.ItemsOf(entries, n).Length")]
        [Ensures("HashSet<T>.ItemsOf(entries, i) == Pal.Slice(HashSet<T>.ItemsOf(entries, n), 0, HashSet<T>.ItemsOf(entries, i).Length)")]
        [PulseBody("HashSetChain.items_prefix $(entries) $(i) $(n)")]
        [Conditional("PAL")]
        private static void ItemsPrefix(Seq<Entry> entries, SpecInt i, SpecInt n) { }

        [Spec]
        [PulseBody("HashSetChain.prefixes $(entries) $(count)")]
        private static Seq<Seq<T>> PrefixesOf(Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        /// <summary><paramref name="prefixes"/> are the prefixes of a walk ending at <paramref name="items"/>.</summary>
        [Spec]
        [PulseBody("HashSetChain.walk $(prefixes) $(items)")]
        internal static bool Walk(Seq<Seq<T>> prefixes, Seq<T> items) => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= count && count <= entries.Length")]
        [Ensures("HashSet<T>.PrefixesOf(entries, count).Length == count + 1 && HashSet<T>.PrefixesOf(entries, count)[0].Length == 0")]
        [Ensures("HashSet<T>.Walk(HashSet<T>.PrefixesOf(entries, count), HashSet<T>.ItemsOf(entries, count))")]
        [PulseBody("HashSetChain.prefixes_walk $(entries) $(count)")]
        [Conditional("PAL")]
        private static void PrefixesWalk(Seq<Entry> entries, SpecInt count) { }

        /// <summary>Every element of <paramref name="others"/> is a member of <paramref name="items"/> at <paramref name="comparer"/>.</summary>
        [Spec]
        [PulseBody("HashSetChain.all_in $(comparer) $(items) $(others)")]
        internal static bool AllIn(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Walk(prefixes, whole) && 0 <= i && i < prefixes.Length")]
        [Requires("!HashSet<T>.AllIn(comparer, items, prefixes[i])")]
        [Ensures("!HashSet<T>.AllIn(comparer, items, whole)")]
        [PulseBody("HashSetChain.all_in_walk $(comparer) $(items) $(prefixes) $(whole) $(i)")]
        [Conditional("PAL")]
        private static void AllInWalk(IEqualityComparer<T>? comparer, Seq<T> items, Seq<Seq<T>> prefixes, Seq<T> whole, SpecInt i) { }

        /// <summary>Some element of <paramref name="items"/> is equal to <paramref name="item"/> at <paramref name="comparer"/>.</summary>
        [Spec]
        [PulseBody("HashSetChain.mem $(comparer) $(items) $(item)")]
        public static bool Mem(IEqualityComparer<T>? comparer, Seq<T> items, T item) => throw new InvalidOperationException();

        
        // R30.41. Set relations modulo the comparer (pal/HashSet/HashSetSets.fst). `Equiv` and
        // `Distinct` are hypotheses: the comparer's `Equals` is uninterpreted, and the table's
        // invariant does not make the elements distinct.

        /// <summary><paramref name="comparer"/>'s <c>Equals</c> is an equivalence.</summary>
        [Spec]
        [PulseBody("HashSetSets.equiv $(comparer)")]
        public static bool Equiv(IEqualityComparer<T>? comparer) => throw new InvalidOperationException();

        /// <summary>No two of <paramref name="items"/> are equal at <paramref name="comparer"/>.</summary>
        [Spec]
        [PulseBody("HashSetSets.distinct $(comparer) $(items)")]
        public static bool Distinct(IEqualityComparer<T>? comparer, Seq<T> items) => throw new InvalidOperationException();

        /// <summary><paramref name="items"/> are, modulo <paramref name="comparer"/>, those of <paramref name="before"/> not in <paramref name="others"/>.</summary>
        [Spec]
        [PulseBody("HashSetSets.except $(comparer) $(before) $(others) $(items)")]
        public static bool Except(IEqualityComparer<T>? comparer, Seq<T> before, Seq<T> others, Seq<T> items) => throw new InvalidOperationException();

        /// <summary>Some element of <paramref name="others"/> is a member of <paramref name="items"/>.</summary>
        [Spec]
        [PulseBody("HashSetSets.overlaps $(comparer) $(items) $(others)")]
        public static bool OverlapsSeq(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others) => throw new InvalidOperationException();

        /// <summary>None of the first <paramref name="k"/> of <paramref name="others"/> is a member of <paramref name="items"/>.</summary>
        [Spec]
        [PulseBody("HashSetSets.no_overlap $(comparer) $(items) $(others) $(k)")]
        private static bool NoOverlap(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others, SpecInt k) => throw new InvalidOperationException();

        /// <summary>No element of <paramref name="others"/> is a member of <paramref name="items"/>.</summary>
        [Spec]
        [PulseBody("HashSetSets.none_in $(comparer) $(items) $(others)")]
        private static bool NoneIn(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others) => throw new InvalidOperationException();

        [Lemma]
        [Ensures("HashSet<T>.Except(comparer, items, Pal.Slice(others, 0, 0), items)")]
        [PulseBody("HashSetSets.except_start $(comparer) $(items) $(others)")]
        [Conditional("PAL")]
        private static void ExceptStart(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others) { }

        [Lemma]
        [Requires("0 <= k && k < others.Length")]
        [Ensures("Pal.Implies(HashSet<T>.Equiv(comparer) && HashSet<T>.Distinct(comparer, items) && HashSet<T>.Except(comparer, before, Pal.Slice(others, 0, k), items) && " +
            "(HashSet<T>.Removed(comparer, items, after, others[k]) || (!HashSet<T>.Mem(comparer, items, others[k]) && after == items)), " +
            "HashSet<T>.Distinct(comparer, after) && HashSet<T>.Except(comparer, before, Pal.Slice(others, 0, k + 1), after))")]
        [PulseBody("HashSetSets.except_step_imp $(comparer) $(before) $(others) $(items) $(after) $(k)")]
        [Conditional("PAL")]
        private static void ExceptStep(IEqualityComparer<T>? comparer, Seq<T> before, Seq<T> others, Seq<T> items, Seq<T> after, SpecInt k) { }

        [Lemma]
        [Ensures("Pal.Implies(HashSet<T>.Except(comparer, before, Pal.Slice(others, 0, others.Length), items), HashSet<T>.Except(comparer, before, others, items))")]
        [PulseBody("HashSetSets.except_done_imp $(comparer) $(before) $(others) $(items)")]
        [Conditional("PAL")]
        private static void ExceptDone(IEqualityComparer<T>? comparer, Seq<T> before, Seq<T> others, Seq<T> items) { }

        [Lemma]
        [Requires("items.Length == 0")]
        [Ensures("HashSet<T>.Except(comparer, items, others, items) && HashSet<T>.Distinct(comparer, items)")]
        [PulseBody("HashSetSets.except_empty $(comparer) $(items) $(others)")]
        [Conditional("PAL")]
        private static void ExceptEmpty(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others) { }

        [Lemma]
        [Requires("0 <= k && k < others.Length && HashSet<T>.Mem(comparer, items, others[k])")]
        [Ensures("HashSet<T>.OverlapsSeq(comparer, items, others)")]
        [PulseBody("HashSetSets.overlaps_hit $(comparer) $(items) $(others) $(k)")]
        [Conditional("PAL")]
        private static void OverlapsHit(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others, SpecInt k) { }

        [Lemma]
        [Requires("0 <= k && k < others.Length && HashSet<T>.NoOverlap(comparer, items, others, k) && !HashSet<T>.Mem(comparer, items, others[k])")]
        [Ensures("HashSet<T>.NoOverlap(comparer, items, others, k + 1)")]
        [PulseBody("HashSetSets.no_overlap_step $(comparer) $(items) $(others) $(k)")]
        [Conditional("PAL")]
        private static void NoOverlapStep(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others, SpecInt k) { }

        [Lemma]
        [Requires("HashSet<T>.NoOverlap(comparer, items, others, others.Length)")]
        [Ensures("!HashSet<T>.OverlapsSeq(comparer, items, others)")]
        [PulseBody("HashSetSets.no_overlap_done $(comparer) $(items) $(others)")]
        [Conditional("PAL")]
        private static void NoOverlapDone(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others) { }

        [Lemma]
        [Requires("HashSet<T>.Walk(prefixes, whole) && 0 <= i && i < prefixes.Length && prefixes[i].Length > 0")]
        [Requires("HashSet<T>.Mem(comparer, items, prefixes[i][prefixes[i].Length - 1])")]
        [Ensures("HashSet<T>.OverlapsSeq(comparer, items, whole)")]
        [PulseBody("HashSetSets.overlaps_walk $(comparer) $(items) $(prefixes) $(whole) $(i)")]
        [Conditional("PAL")]
        private static void OverlapsWalk(IEqualityComparer<T>? comparer, Seq<T> items, Seq<Seq<T>> prefixes, Seq<T> whole, SpecInt i) { }

        [Lemma]
        [Requires("HashSet<T>.Walk(prefixes, whole) && HashSet<T>.NoneIn(comparer, items, prefixes[prefixes.Length - 1])")]
        [Ensures("!HashSet<T>.OverlapsSeq(comparer, items, whole)")]
        [PulseBody("HashSetSets.none_in_walk $(comparer) $(items) $(prefixes) $(whole)")]
        [Conditional("PAL")]
        private static void NoneInWalk(IEqualityComparer<T>? comparer, Seq<T> items, Seq<Seq<T>> prefixes, Seq<T> whole) { }

        [Lemma]
        [Ensures("Pal.Implies(HashSet<T>.Equiv(comparer), HashSet<T>.AllIn(comparer, items, items))")]
        [PulseBody("HashSetSets.all_in_refl_imp $(comparer) $(items)")]
        [Conditional("PAL")]
        private static void AllInRefl(IEqualityComparer<T>? comparer, Seq<T> items) { }

        [Lemma]
        [Ensures("Pal.Implies(HashSet<T>.Equiv(comparer) && HashSet<T>.Distinct(comparer, items) && HashSet<T>.AllIn(comparer, before, items) && " +
            "(HashSet<T>.Removed(comparer, items, after, item) || after == items), " +
            "HashSet<T>.Distinct(comparer, after) && HashSet<T>.AllIn(comparer, before, after))")]
        [PulseBody("HashSetSets.remove_where_step_imp $(comparer) $(before) $(items) $(after) $(item)")]
        [Conditional("PAL")]
        private static void RemoveWhereStep(IEqualityComparer<T>? comparer, Seq<T> before, Seq<T> items, Seq<T> after, T item) { }

        /// <summary>The pigeonhole principle modulo an equivalence: distinct members of <paramref name="items"/> are no more than its length.</summary>
        [Lemma]
        [Requires("HashSet<T>.Equiv(comparer) && HashSet<T>.Distinct(comparer, others) && HashSet<T>.AllIn(comparer, items, others)")]
        [Ensures("others.Length <= items.Length")]
        [PulseBody("HashSetSets.pigeonhole $(comparer) $(others) $(items)")]
        [Conditional("PAL")]
        private static void PigeonHole(IEqualityComparer<T>? comparer, Seq<T> items, Seq<T> others) { }

        [Spec]
        [PulseBody("HashSetChain.bucket $(buckets) $(entries) $(comparer) $(item)")]
        private static SpecInt Bucket(Seq<int> buckets, Seq<Entry> entries, IEqualityComparer<T>? comparer, T item)
            => throw new InvalidOperationException();

        [Spec]
        [PulseBody("HashSetChain.search $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q)")]
        private static bool Search(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item, SpecInt i, SpecInt q) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("HashSetChain.hit $(entries) $(comparer) $(item) $(i)")]
        private static bool Hit(Seq<Entry> entries, IEqualityComparer<T>? comparer, T item, SpecInt i)
            => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Wf(buckets, entries, count, freeList, freeCount, comparer) && entries.Length > 0")]
        [Ensures("HashSet<T>.Search(buckets, entries, count, freeList, freeCount, comparer, item, HashSet<T>.Bucket(buckets, entries, comparer, item) - 1, 0)")]
        [Ensures("0 <= HashSet<T>.Bucket(buckets, entries, comparer, item) && HashSet<T>.Bucket(buckets, entries, comparer, item) <= entries.Length")]
        [PulseBody("HashSetChain.search_start $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item)")]
        [Conditional("PAL")]
        private static void SearchStart(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item) { }

        [Lemma]
        [Requires("HashSet<T>.Search(buckets, entries, count, freeList, freeCount, comparer, item, i, q)")]
        [Requires("0 <= i && i < entries.Length && !HashSet<T>.Hit(entries, comparer, item, i)")]
        [Ensures("HashSet<T>.Search(buckets, entries, count, freeList, freeCount, comparer, item, entries[i].Next, q + 1)")]
        [Ensures("q + 1 <= entries.Length")]
        [PulseBody("HashSetChain.search_step $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchStep(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item, SpecInt i, SpecInt q) { }

        [Lemma]
        [Requires("HashSet<T>.Search(buckets, entries, count, freeList, freeCount, comparer, item, i, q)")]
        [Requires("HashSet<T>.Hit(entries, comparer, item, i)")]
        [Ensures("HashSet<T>.Mem(comparer, HashSet<T>.ItemsOf(entries, count), item)")]
        [PulseBody("HashSetChain.search_hit $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchHit(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item, SpecInt i, SpecInt q) { }

        [Lemma]
        [Requires("HashSet<T>.Search(buckets, entries, count, freeList, freeCount, comparer, item, i, q)")]
        [Requires("!(0 <= i && i < entries.Length)")]
        [Ensures("!HashSet<T>.Mem(comparer, HashSet<T>.ItemsOf(entries, count), item)")]
        [PulseBody("HashSetChain.search_absent $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q)")]
        [Conditional("PAL")]
        private static void SearchAbsent(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item, SpecInt i, SpecInt q) { }

        [Spec]
        [PulseBody("HashSetChain.search_last $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q) $(last)")]
        private static bool SearchLast(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item, SpecInt i, SpecInt q, SpecInt last) => throw new InvalidOperationException();

        /// <summary><paramref name="after"/> is <paramref name="before"/> without one element equal to <paramref name="item"/>.</summary>
        [Spec]
        [PulseBody("HashSetChain.removed $(comparer) $(before) $(after) $(item)")]
        public static bool Removed(IEqualityComparer<T>? comparer, Seq<T> before, Seq<T> after, T item) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("HashSetChain.remove_writes $(buckets) $(buckets1) $(entries) $(entries1) $(comparer) $(item) $(freeList) $(i) $(last)")]
        private static bool RemoveWrites(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1,
            IEqualityComparer<T>? comparer, T item, SpecInt freeList, SpecInt i, SpecInt last) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Wf(buckets, entries, count, freeList, freeCount, comparer) && entries.Length > 0")]
        [Ensures("HashSet<T>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, item, HashSet<T>.Bucket(buckets, entries, comparer, item) - 1, 0, -1)")]
        [PulseBody("HashSetChain.search_last_start $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item)")]
        [Conditional("PAL")]
        private static void SearchLastStart(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item) { }

        [Lemma]
        [Requires("HashSet<T>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, item, i, q, last)")]
        [Requires("0 <= i && i < entries.Length && !HashSet<T>.Hit(entries, comparer, item, i)")]
        [Ensures("HashSet<T>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, item, entries[i].Next, q + 1, i)")]
        [Ensures("q + 1 <= entries.Length")]
        [PulseBody("HashSetChain.search_last_step $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q) $(last)")]
        [Conditional("PAL")]
        private static void SearchLastStep(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item, SpecInt i, SpecInt q, SpecInt last) { }

        [Lemma]
        [Requires("HashSet<T>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, item, i, q, last)")]
        [Requires("!(0 <= i && i < entries.Length)")]
        [Ensures("!HashSet<T>.Mem(comparer, HashSet<T>.ItemsOf(entries, count), item)")]
        [PulseBody("HashSetChain.search_last_absent $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q) $(last)")]
        [Conditional("PAL")]
        private static void SearchLastAbsent(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item, SpecInt i, SpecInt q, SpecInt last) { }

        [Lemma]
        [Requires("HashSet<T>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, item, i, q, last)")]
        [Requires("0 <= i && i < entries.Length")]
        [Ensures("-1 <= entries[i].Next && entries[i].Next < entries.Length")]
        [Ensures("-1 <= freeList && freeList < entries.Length")]
        [Ensures("last < 0 || (0 <= last && last < entries.Length && last != i)")]
        [PulseBody("HashSetChain.search_next $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q) $(last)")]
        [Conditional("PAL")]
        private static void SearchNext(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item, SpecInt i, SpecInt q, SpecInt last) { }

        [Lemma]
        [Requires("HashSet<T>.SearchLast(buckets, entries, count, freeList, freeCount, comparer, item, i, q, last)")]
        [Requires("HashSet<T>.Hit(entries, comparer, item, i)")]
        [Requires("HashSet<T>.RemoveWrites(buckets, buckets1, entries, entries1, comparer, item, freeList, i, last)")]
        [Ensures("HashSet<T>.Wf(buckets1, entries1, count, i, freeCount + 1, comparer) && freeCount + 1 <= count")]
        [Ensures("HashSet<T>.Mem(comparer, HashSet<T>.ItemsOf(entries, count), item)")]
        [Ensures("HashSet<T>.Removed(comparer, HashSet<T>.ItemsOf(entries, count), HashSet<T>.ItemsOf(entries1, count), item)")]
        [PulseBody("HashSetChain.remove_ok $(buckets) $(buckets1) $(entries) $(entries1) $(count) $(freeList) $(freeCount) $(comparer) $(item) $(i) $(q) $(last)")]
        [Conditional("PAL")]
        private static void RemoveOk(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1,
            SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<T>? comparer, T item,
            SpecInt i, SpecInt q, SpecInt last) { }

        // The growth path (pal/HashSet/HashSetChain.fst, Pulse.Lib.CSharp.HashInsert).
        [Spec]
        [PulseBody("HashSetChain.zeros $(buckets)")]
        private static bool Zeros(Seq<int> buckets) => throw new InvalidOperationException();

        [Lemma]
        [Requires("buckets.Length == entries.Length && HashSet<T>.Zeros(buckets)")]
        [Ensures("HashSet<T>.Wf(buckets, entries, 0, -1, 0, comparer) && HashSet<T>.ItemsOf(entries, 0) == Pal.EmptySeq<T>()")]
        [PulseBody("HashSetChain.wf_fresh $(buckets) $(entries) $(comparer)")]
        [Conditional("PAL")]
        private static void WfFresh(Seq<int> buckets, Seq<Entry> entries, IEqualityComparer<T>? comparer) { }

        /// <summary><paramref name="after"/> is <paramref name="before"/> with <paramref name="item"/> inserted somewhere.</summary>
        [Spec]
        [PulseBody("HashSetChain.added $(before) $(after) $(item)")]
        public static bool Added(Seq<T> before, Seq<T> after, T item) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("HashSetChain.fnext $(entries) $(i)")]
        private static SpecInt FNext(Seq<Entry> entries, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Wf(buckets, entries, count, freeList, freeCount, comparer) && entries.Length > 0")]
        [Ensures("0 <= HashSet<T>.Bucket(buckets, entries, comparer, item) && HashSet<T>.Bucket(buckets, entries, comparer, item) <= entries.Length")]
        [Ensures("Pal.Implies(freeCount > 0, 0 <= freeList && freeList < count && -1 <= HashSet<T>.FNext(entries, freeList) && HashSet<T>.FNext(entries, freeList) < count)")]
        [Ensures("Pal.Implies(freeCount == 0, freeList == -1) && freeCount <= count")]
        [PulseBody("HashSetChain.insert_pre $(buckets) $(entries) $(count) $(freeList) $(freeCount) $(comparer) $(item)")]
        [Conditional("PAL")]
        private static void InsertPre(Seq<int> buckets, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer, T item) { }

        [Spec]
        [PulseBody("HashSetChain.insert_writes $(buckets) $(buckets1) $(entries) $(entries1) $(comparer) $(item) $(i)")]
        private static bool InsertWrites(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1,
            IEqualityComparer<T>? comparer, T item, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.InsertWrites(buckets, buckets1, entries, entries1, comparer, item, i)")]
        [Requires("(count1 == count && freeCount1 >= 0 && HashSet<T>.Wf(buckets, entries, count, i, freeCount1 + 1, comparer) && freeList1 == HashSet<T>.FNext(entries, i)) || (freeCount1 == 0 && i == count && count1 == count + 1 && HashSet<T>.Wf(buckets, entries, count, freeList1, 0, comparer))")]
        [Ensures("HashSet<T>.Wf(buckets1, entries1, count1, freeList1, freeCount1, comparer)")]
        [Ensures("HashSet<T>.Added(HashSet<T>.ItemsOf(entries, count), HashSet<T>.ItemsOf(entries1, count1), item)")]
        [Ensures("HashSet<T>.ItemsOf(entries1, count1).Length == HashSet<T>.ItemsOf(entries, count).Length + 1")]
        [PulseBody("HashSetChain.insert_ok $(buckets) $(buckets1) $(entries) $(entries1) $(count) $(count1) $(freeList1) $(freeCount1) $(i) $(comparer) $(item)")]
        [Conditional("PAL")]
        private static void InsertOk(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1,
            SpecInt count, SpecInt count1, SpecInt freeList1, SpecInt freeCount1, SpecInt i,
            IEqualityComparer<T>? comparer, T item) { }

        [Spec]
        [PulseBody("HashSetChain.same_prefix $(old) $(entries) $(count)")]
        private static bool SamePrefix(Seq<Entry> old, Seq<Entry> entries, SpecInt count) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("HashSetChain.pre_wf $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        private static bool PreWf(Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount,
            IEqualityComparer<T>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Wf(buckets, old, count, freeList, freeCount, comparer) && HashSet<T>.SamePrefix(old, entries, count)")]
        [Ensures("HashSet<T>.PreWf(entries, count, freeList, freeCount, comparer) && HashSet<T>.ItemsOf(entries, count) == HashSet<T>.ItemsOf(old, count)")]
        [PulseBody("HashSetChain.copy_ok $(buckets) $(old) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void CopyOk(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, SpecInt freeList,
            SpecInt freeCount, IEqualityComparer<T>? comparer) { }

        [Spec]
        [PulseBody("HashSetChain.rebuilt $(buckets) $(source) $(entries) $(count) $(i)")]
        private static bool Rebuilt(Seq<int> buckets, Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt i)
            => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= count && count <= source.Length && source.Length > 0 && buckets.Length == source.Length && HashSet<T>.Zeros(buckets)")]
        [Ensures("HashSet<T>.Rebuilt(buckets, source, source, count, 0)")]
        [PulseBody("HashSetChain.rebuild_start $(buckets) $(source) $(count)")]
        [Conditional("PAL")]
        private static void RebuildStart(Seq<int> buckets, Seq<Entry> source, SpecInt count) { }

        [Spec]
        [PulseBody("HashSetChain.slot $(buckets) $(entries) $(i)")]
        private static SpecInt Slot(Seq<int> buckets, Seq<Entry> entries, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Rebuilt(buckets, source, entries, count, i) && i < count")]
        [Ensures("0 <= HashSet<T>.Slot(buckets, entries, i) && HashSet<T>.Slot(buckets, entries, i) <= entries.Length")]
        [PulseBody("HashSetChain.rebuild_bucket $(buckets) $(source) $(entries) $(count) $(i)")]
        [Conditional("PAL")]
        private static void RebuildBucket(Seq<int> buckets, Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt i) { }

        [Spec]
        [PulseBody("HashSetChain.link_writes $(buckets) $(buckets1) $(entries) $(entries1) $(i)")]
        private static bool LinkWrites(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> entries, Seq<Entry> entries1, SpecInt i)
            => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Rebuilt(buckets, source, entries, count, i) && i < count && HashSet<T>.LinkWrites(buckets, buckets1, entries, entries1, i)")]
        [Ensures("HashSet<T>.Rebuilt(buckets1, source, entries1, count, i + 1)")]
        [PulseBody("HashSetChain.rebuild_step $(buckets) $(buckets1) $(source) $(entries) $(entries1) $(count) $(i)")]
        [Conditional("PAL")]
        private static void RebuildStep(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> source, Seq<Entry> entries,
            Seq<Entry> entries1, SpecInt count, SpecInt i) { }

        [Lemma]
        [Requires("HashSet<T>.PreWf(source, count, freeList, freeCount, comparer) && HashSet<T>.Rebuilt(buckets, source, entries, count, count)")]
        [Ensures("HashSet<T>.Wf(buckets, entries, count, freeList, freeCount, comparer) && HashSet<T>.ItemsOf(entries, count) == HashSet<T>.ItemsOf(source, count)")]
        [PulseBody("HashSetChain.rebuild_done $(buckets) $(source) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void RebuildDone(Seq<int> buckets, Seq<Entry> source, Seq<Entry> entries, SpecInt count,
            SpecInt freeList, SpecInt freeCount, IEqualityComparer<T>? comparer) { }

        // Compacting into new arrays (`CopyEntries`, for `TrimExcess`).
        [Spec]
        [PulseBody("HashSetChain.compactable $(old) $(count) $(comparer)")]
        private static bool Compactable(Seq<Entry> old, SpecInt count, IEqualityComparer<T>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Wf(buckets, old, count, freeList, freeCount, comparer) && 0 <= freeCount && freeCount <= count")]
        [Ensures("HashSet<T>.Compactable(old, count, comparer) && HashSet<T>.ItemsOf(old, count).Length == count - freeCount")]
        [PulseBody("HashSetChain.wf_compactable $(buckets) $(old) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void WfCompactable(Seq<int> buckets, Seq<Entry> old, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<T>? comparer) { }

        [Spec]
        [PulseBody("HashSetChain.compacted $(buckets) $(old) $(entries) $(count) $(i) $(m) $(comparer)")]
        private static bool Compacted(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, SpecInt i, SpecInt m, IEqualityComparer<T>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Compactable(old, count, comparer) && entries.Length > 0 && buckets.Length == entries.Length && HashSet<T>.Zeros(buckets) && HashSet<T>.ItemsOf(old, count).Length <= entries.Length")]
        [Ensures("HashSet<T>.Compacted(buckets, old, entries, count, 0, 0, comparer)")]
        [PulseBody("HashSetChain.compact_start $(buckets) $(old) $(entries) $(count) $(comparer)")]
        [Conditional("PAL")]
        private static void CompactStart(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, IEqualityComparer<T>? comparer) { }

        [Spec]
        [PulseBody("HashSetChain.old_slot $(buckets) $(old) $(entries) $(i)")]
        private static SpecInt OldSlot(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt i) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Compacted(buckets, old, entries, count, i, m, comparer) && i < count && old[i].Next >= -1")]
        [Ensures("0 <= m && m < entries.Length && 0 <= HashSet<T>.OldSlot(buckets, old, entries, i) && HashSet<T>.OldSlot(buckets, old, entries, i) <= entries.Length")]
        [PulseBody("HashSetChain.compact_room $(buckets) $(old) $(entries) $(count) $(i) $(m) $(comparer)")]
        [Conditional("PAL")]
        private static void CompactRoom(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, SpecInt i, SpecInt m, IEqualityComparer<T>? comparer) { }

        [Spec]
        [PulseBody("HashSetChain.compact_writes $(buckets) $(buckets1) $(old) $(entries) $(entries1) $(i) $(m) $(m1)")]
        private static bool CompactWrites(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> old, Seq<Entry> entries, Seq<Entry> entries1, SpecInt i, SpecInt m, SpecInt m1) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Compacted(buckets, old, entries, count, i, m, comparer) && i < count && HashSet<T>.CompactWrites(buckets, buckets1, old, entries, entries1, i, m, m1)")]
        [Ensures("HashSet<T>.Compacted(buckets1, old, entries1, count, i + 1, m1, comparer)")]
        [PulseBody("HashSetChain.compact_step $(buckets) $(buckets1) $(old) $(entries) $(entries1) $(count) $(i) $(m) $(m1) $(comparer)")]
        [Conditional("PAL")]
        private static void CompactStep(Seq<int> buckets, Seq<int> buckets1, Seq<Entry> old, Seq<Entry> entries, Seq<Entry> entries1, SpecInt count, SpecInt i, SpecInt m, SpecInt m1, IEqualityComparer<T>? comparer) { }

        [Lemma]
        [Requires("HashSet<T>.Compacted(buckets, old, entries, count, count, m, comparer)")]
        [Ensures("HashSet<T>.Wf(buckets, entries, m, -1, 0, comparer) && HashSet<T>.ItemsOf(entries, m) == HashSet<T>.ItemsOf(old, count) && m <= entries.Length && HashSet<T>.ItemsOf(entries, m).Length == m")]
        [PulseBody("HashSetChain.compact_done $(buckets) $(old) $(entries) $(count) $(m) $(comparer)")]
        [Conditional("PAL")]
        private static void CompactDone(Seq<int> buckets, Seq<Entry> old, Seq<Entry> entries, SpecInt count, SpecInt m, IEqualityComparer<T>? comparer) { }

        // The collision path: a string set switches to the randomized comparer and rehashes.
        [Spec]
        [PulseBody("HashSetChain.non_randomized $(comparer)")]
        private static bool NonRandomized(IEqualityComparer<T>? comparer) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("HashSetChain.randomized $(comparer)")]
        private static IEqualityComparer<T>? Randomized(IEqualityComparer<T>? comparer) => throw new InvalidOperationException();

        /// <summary>Whether two comparers deem the same elements equal.</summary>
        [Spec]
        [PulseBody("HashSetChain.same_equality $(comparer1) $(comparer2)")]
        public static bool SameEquality(IEqualityComparer<T>? comparer1, IEqualityComparer<T>? comparer2) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.NonRandomized(comparer)")]
        [Ensures("HashSet<T>.SameEquality(comparer, HashSet<T>.Randomized(comparer)) && HashSet<T>.Randomized(comparer) != null")]
        [PulseBody("HashSetChain.randomized_same $(comparer)")]
        [Conditional("PAL")]
        private static void RandomizedSame(IEqualityComparer<T>? comparer) { }

        /// <summary>
        /// Swapping a string set's comparer for what <c>GetStringComparer</c> returned keeps its
        /// equality.
        /// </summary>
        [Spec]
        [PulseBody("HashSetChain.string_swap_ok $(comparer)")]
        private static bool StringSwapOk(IEqualityComparer<T>? comparer) => throw new InvalidOperationException();

        [Lemma]
        [Ensures("HashSet<T>.StringSwapOk(comparer)")]
        [PulseBody("HashSetChain.string_swap $(comparer)")]
        [Conditional("PAL")]
        private static void StringSwap(IEqualityComparer<T>? comparer) { }

        [Lemma]
        [Ensures("HashSet<T>.SameEquality(comparer, comparer)")]
        [PulseBody("HashSetChain.same_refl $(comparer)")]
        [Conditional("PAL")]
        private static void SameRefl(IEqualityComparer<T>? comparer) { }

        /// <summary>Membership is the same under two comparers with the same equality.</summary>
        [Lemma]
        [Requires("HashSet<T>.SameEquality(comparer1, comparer2)")]
        [Ensures("HashSet<T>.Mem(comparer1, items, item) == HashSet<T>.Mem(comparer2, items, item)")]
        [PulseBody("HashSetChain.mem_same $(comparer1) $(comparer2) $(items) $(item)")]
        [Conditional("PAL")]
        public static void MemSame(IEqualityComparer<T>? comparer1, IEqualityComparer<T>? comparer2, Seq<T> items, T item) { }

        [Lemma]
        [Requires("HashSet<T>.NonRandomized(comparer) && HashSet<T>.Added(before, after, item)")]
        [Ensures("HashSet<T>.Mem(comparer, after, item)")]
        [PulseBody("(HashSetChain.non_randomized_refl $(comparer) $(item); HashSetChain.added_mem $(comparer) $(before) $(after) $(item))")]
        [Conditional("PAL")]
        private static void AddedMem(IEqualityComparer<T>? comparer, Seq<T> before, Seq<T> after, T item) { }

        [Spec]
        [PulseBody("HashSetChain.rehashed $(source) $(entries) $(count) $(i) $(comparer)")]
        private static bool Rehashed(Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt i, IEqualityComparer<T>? comparer)
            => throw new InvalidOperationException();

        [Lemma]
        [Requires("0 <= count && count <= source.Length")]
        [Ensures("HashSet<T>.Rehashed(source, source, count, 0, comparer)")]
        [PulseBody("HashSetChain.rehash_start $(source) $(count) $(comparer)")]
        [Conditional("PAL")]
        private static void RehashStart(Seq<Entry> source, SpecInt count, IEqualityComparer<T>? comparer) { }

        [Spec]
        [PulseBody("HashSetChain.rehash_writes $(entries) $(entries1) $(i) $(comparer)")]
        private static bool RehashWrites(Seq<Entry> entries, Seq<Entry> entries1, SpecInt i, IEqualityComparer<T>? comparer)
            => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.Rehashed(source, entries, count, i, comparer) && i < count && HashSet<T>.RehashWrites(entries, entries1, i, comparer)")]
        [Ensures("HashSet<T>.Rehashed(source, entries1, count, i + 1, comparer)")]
        [PulseBody("HashSetChain.rehash_step $(source) $(entries) $(entries1) $(count) $(i) $(comparer)")]
        [Conditional("PAL")]
        private static void RehashStep(Seq<Entry> source, Seq<Entry> entries, Seq<Entry> entries1, SpecInt count, SpecInt i,
            IEqualityComparer<T>? comparer) { }

        /// <summary>The field <paramref name="field"/> holds the non-null comparer <paramref name="comparer"/>.</summary>
        [Spec]
        [PulseBody("($(field) == Some $(comparer))")]
        private static bool Holds(IEqualityComparer<T>? field, IEqualityComparer<T> comparer) => throw new InvalidOperationException();

        [Spec]
        [PulseBody("HashSetChain.pre_free $(entries) $(count) $(freeList) $(freeCount)")]
        private static bool PreFree(Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount) => throw new InvalidOperationException();

        [Lemma]
        [Requires("HashSet<T>.PreWf(entries, count, freeList, freeCount, comparer)")]
        [Ensures("HashSet<T>.PreFree(entries, count, freeList, freeCount)")]
        [PulseBody("HashSetChain.pre_free_of $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void PreFreeOf(Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount, IEqualityComparer<T>? comparer) { }

        [Lemma]
        [Requires("HashSet<T>.PreFree(source, count, freeList, freeCount) && HashSet<T>.Rehashed(source, entries, count, count, comparer)")]
        [Ensures("HashSet<T>.PreWf(entries, count, freeList, freeCount, comparer) && HashSet<T>.ItemsOf(entries, count) == HashSet<T>.ItemsOf(source, count)")]
        [PulseBody("HashSetChain.rehash_done $(source) $(entries) $(count) $(freeList) $(freeCount) $(comparer)")]
        [Conditional("PAL")]
        private static void RehashDone(Seq<Entry> source, Seq<Entry> entries, SpecInt count, SpecInt freeList, SpecInt freeCount,
            IEqualityComparer<T>? comparer) { }

        /// <summary>The number of elements.</summary>
        [Spec]
        public SpecInt SpecCount => Model.Count;

        #region Constructors

        [Ensures("@this.SpecCount == 0 && @this.SpecItems == Pal.EmptySeq<T>() && @this.SpecSlots == 0 && @this.SpecVersion == 0")]
        [Ensures("HashSet<T>.SameEquality(null, @this.SpecComparer)")]
        public HashSet() : this((IEqualityComparer<T>?)null) { }

        [Ensures("@this.SpecCount == 0 && @this.SpecItems == Pal.EmptySeq<T>() && @this.SpecSlots == 0 && @this.SpecVersion == 0")]
        [Ensures("HashSet<T>.SameEquality(comparer, @this.SpecComparer)")]
        public HashSet(IEqualityComparer<T>? comparer)
        {
            // For reference types, we always want to store a comparer instance, either
            // the one provided, or if one wasn't provided, the default (accessing
            // EqualityComparer<TKey>.Default with shared generics on every dictionary
            // access can add measurable overhead).  For value types, if no comparer is
            // provided, or if the default is provided, we'd prefer to use
            // EqualityComparer<TKey>.Default.Equals on every use, enabling the JIT to
            // devirtualize and possibly inline the operation.
            if (!typeof(T).IsValueType)
            {
                _comparer = comparer ?? EqualityComparer<T>.Default;

                // Special-case EqualityComparer<string>.Default, StringComparer.Ordinal, and StringComparer.OrdinalIgnoreCase.
                // We use a non-randomized comparer for improved perf, falling back to a randomized comparer if the
                // hash buckets become unbalanced.
                if (typeof(T) == typeof(string) &&
                    NonRandomizedStringEqualityComparer.GetStringComparer(_comparer) is IEqualityComparer<string> stringComparer)
                {
                    StringSwap(_comparer);
                    _comparer = (IEqualityComparer<T>)stringComparer;
                }
            }
            else if (comparer is not null && // first check for null to avoid forcing default comparer instantiation unnecessarily
                     comparer != EqualityComparer<T>.Default)
            {
                _comparer = comparer;
            }
        }

        [Requires("capacity <= 0x7FFFFFC3")]
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == 0 && @this.SpecItems == Pal.EmptySeq<T>() && @this.SpecSlots == 0 && @this.SpecVersion == 0")]
        [Ensures("capacity <= @this.SpecCapacity && HashSet<T>.SameEquality(null, @this.SpecComparer)")]
        public HashSet(int capacity) : this(capacity, null) { }

        public HashSet(IEnumerable<T> collection) : this(collection, null) { }

        public HashSet(IEnumerable<T> collection, IEqualityComparer<T>? comparer) : this(comparer)
        {
            if (collection == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.collection);
            }

            if (collection is HashSet<T> otherAsHashSet && EffectiveEqualityComparersAreEqual(this, otherAsHashSet))
            {
                ConstructFrom(otherAsHashSet);
            }
            else
            {
                // To avoid excess resizes, first set size based on collection's count. The collection may
                // contain duplicates, so call TrimExcess if resulting HashSet is larger than the threshold.
                if (collection is ICollection<T> coll)
                {
                    int count = coll.Count;
                    if (count > 0)
                    {
                        Initialize(count);
                    }
                }

                UnionWith(collection);

                if (_count > 0 && _entries!.Length / _count > ShrinkThreshold)
                {
                    TrimExcess();
                }
            }
        }

        [Requires("capacity <= 0x7FFFFFC3")]
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("@this.SpecCount == 0 && @this.SpecItems == Pal.EmptySeq<T>() && @this.SpecSlots == 0 && @this.SpecVersion == 0")]
        [Ensures("capacity <= @this.SpecCapacity && HashSet<T>.SameEquality(comparer, @this.SpecComparer)")]
        public HashSet(int capacity, IEqualityComparer<T>? comparer) : this(comparer)
        {
            if (capacity < 0)
            {
                ThrowHelper.ThrowArgumentOutOfRangeException(ExceptionArgument.capacity);
            }

            if (capacity > 0)
            {
                Initialize(capacity);
            }
        }

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        [EditorBrowsable(EditorBrowsableState.Never)]
        protected HashSet(SerializationInfo info, StreamingContext context)
        {
            // We can't do anything with the keys and values until the entire graph has been
            // deserialized and we have a reasonable estimate that GetHashCode is not going to
            // fail.  For the time being, we'll just cache this.  The graph is not valid until
            // OnDeserialization has been called.
            HashHelpers.SerializationInfoTable.Add(this, info);
        }

        /// <summary>Initializes the HashSet from another HashSet with the same element type and equality comparer.</summary>
        private void ConstructFrom(HashSet<T> source)
        {
            Debug.Assert(EffectiveEqualityComparersAreEqual(this, source), "must use identical effective comparers.");

            if (source.Count == 0)
            {
                // As well as short-circuiting on the rest of the work done,
                // this avoids errors from trying to access source._buckets
                // or source._entries when they aren't initialized.
                return;
            }

            int capacity = source._buckets!.Length;
            int threshold = HashHelpers.ExpandPrime(source.Count + 1);

            if (threshold >= capacity)
            {
                _buckets = (int[])source._buckets.Clone();
                _entries = (Entry[])source._entries!.Clone();
                _freeList = source._freeList;
                _freeCount = source._freeCount;
                _count = source._count;
#if TARGET_64BIT
                _fastModMultiplier = source._fastModMultiplier;
#endif
            }
            else
            {
                Initialize(source.Count);
                CopyEntries(source._entries!, source._count);
            }

            Debug.Assert(Count == source.Count);
        }

        #endregion

        #region ICollection<T> methods

        [Requires("@this.SpecSlots < 0x7FFFFFC3")]
        [Ensures("(HashSet<T>.Added(Old(@this.SpecItems), @this.SpecItems, item) && @this.SpecCount == Old(@this.SpecCount) + 1) || (@this.SpecItems == Old(@this.SpecItems) && @this.SpecCount == Old(@this.SpecCount) && HashSet<T>.Mem(@this.SpecComparer, @this.SpecItems, item))")]
        [Ensures("HashSet<T>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        void ICollection<T>.Add(T item) => AddIfNotPresent(item, out _);

        /// <summary>Removes all elements from the <see cref="HashSet{T}"/> object.</summary>
        [Ensures("@this.SpecCount == 0")]
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

        /// <summary>Determines whether the <see cref="HashSet{T}"/> contains the specified element.</summary>
        /// <param name="item">The element to locate in the <see cref="HashSet{T}"/> object.</param>
        /// <returns>true if the <see cref="HashSet{T}"/> object contains the specified element; otherwise, false.</returns>
        [Ensures("Implies(Result, HashSet<T>.Mem(@this.SpecComparer, @this.SpecItems, item))")]
        [Ensures("Implies(!Result, !HashSet<T>.Mem(@this.SpecComparer, @this.SpecItems, item))")]
        public bool Contains(T item) => FindItemIndex(item) >= 0;

        /// <summary>Gets the index of the item in <see cref="_entries"/>, or -1 if it's not in the set.</summary>
        [Ensures("Result >= -1 && Result < @this.SpecCapacity")]
        [Ensures("Implies(Result >= 0, HashSet<T>.Mem(@this.SpecComparer, @this.SpecItems, item))")]
        [Ensures("Implies(Result < 0, !HashSet<T>.Mem(@this.SpecComparer, @this.SpecItems, item))")]
        [Ensures("@this.SpecItems == Old(@this.SpecItems) && @this.SpecCount == Old(@this.SpecCount) && @this.SpecComparer == Old(@this.SpecComparer)")]
        private int FindItemIndex(T item)
        {
            int[]? buckets = _buckets;
            if (buckets != null)
            {
                Entry[]? entries = _entries;
                Debug.Assert(entries != null, "Expected _entries to be initialized");

                uint collisionCount = 0;
                IEqualityComparer<T>? comparer = _comparer;

                if (typeof(T).IsValueType && // comparer can only be null for value types; enable JIT to eliminate entire if block for ref types
                    comparer == null)
                {
                    // ValueType: Devirtualize with EqualityComparer<TValue>.Default intrinsic
                    int hashCode = item!.GetHashCode();
                    SearchStart(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item);
                    int i = GetBucketRef(hashCode) - 1; // Value in _buckets is 1-based
                    while ((uint)i < (uint)entries.Length)
                    {
                        Pal.Invariant(collisionCount <= (uint)entries.Length);
                        Pal.Invariant(Search(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, item, i, collisionCount));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<int>() >= 0 && Pal.Result<int>() < entries.Length && Mem(_comparer, ItemsOf(Pal.Contents(entries), _count), item)));
                        Pal.Decreases((uint)entries.Length - collisionCount);
                        ref Entry entry = ref entries[i];
                        if (entry.HashCode == hashCode && EqualityComparer<T>.Default.Equals(entry.Value, item))
                        {
                            SearchHit(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount);
                            return i;
                        }
                        SearchStep(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount);
                        i = entry.Next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop, which means a concurrent update has happened.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                    }
                    SearchAbsent(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount);
                }
                else
                {
                    Debug.Assert(comparer is not null);
                    int hashCode = item != null ? comparer.GetHashCode(item) : 0;
                    SearchStart(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item);
                    int i = GetBucketRef(hashCode) - 1; // Value in _buckets is 1-based
                    while ((uint)i < (uint)entries.Length)
                    {
                        Pal.Invariant(collisionCount <= (uint)entries.Length);
                        Pal.Invariant(Search(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, item, i, collisionCount));
                        Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<int>() >= 0 && Pal.Result<int>() < entries.Length && Mem(_comparer, ItemsOf(Pal.Contents(entries), _count), item)));
                        Pal.Decreases((uint)entries.Length - collisionCount);
                        ref Entry entry = ref entries[i];
                        if (entry.HashCode == hashCode && comparer.Equals(entry.Value, item))
                        {
                            SearchHit(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount);
                            return i;
                        }
                        SearchStep(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount);
                        i = entry.Next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop, which means a concurrent update has happened.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                    }
                    SearchAbsent(Pal.Contents(buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount);
                }
            }

            return -1;
        }

        /// <summary>Gets a reference to the specified hashcode's bucket, containing an index into <see cref="_entries"/>.</summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private ref int GetBucketRef(int hashCode)
        {
            int[] buckets = _buckets!;
#if TARGET_64BIT
            return ref buckets[HashHelpers.FastMod((uint)hashCode, (uint)buckets.Length, _fastModMultiplier)];
#else
            return ref buckets[(uint)hashCode % (uint)buckets.Length];
#endif
        }

        [Ensures("Implies(Result, HashSet<T>.Mem(Old(@this.SpecComparer), Old(@this.SpecItems), item))")]
        [Ensures("Implies(Result, HashSet<T>.Removed(Old(@this.SpecComparer), Old(@this.SpecItems), @this.SpecItems, item))")]
        [Ensures("Implies(!Result, !HashSet<T>.Mem(Old(@this.SpecComparer), Old(@this.SpecItems), item))")]
        [Ensures("Implies(!Result, @this.SpecItems == Old(@this.SpecItems))")]
        [Ensures("@this.SpecComparer == Old(@this.SpecComparer)")]
        public bool Remove(T item)
        {
            if (_buckets != null)
            {
                Entry[]? entries = _entries;
                Debug.Assert(entries != null, "entries should be non-null");

                uint collisionCount = 0;
                int last = -1;

                IEqualityComparer<T>? comparer = _comparer;
                Debug.Assert(typeof(T).IsValueType || comparer is not null);
                int hashCode =
                    typeof(T).IsValueType && comparer == null ? item!.GetHashCode() :
                    item is not null ? comparer!.GetHashCode(item) :
                    0;

                Ghost<Seq<T>> items0 = ItemsOf(Pal.Contents(entries), _count);
                Ghost<int> length0 = entries.Length; // the measure may not name a field the loop writes (F3)
                SearchLastStart(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item);
                ref int bucket = ref GetBucketRef(hashCode);
                int i = bucket - 1; // Value in buckets is 1-based

                while ((uint)i < (uint)entries.Length)
                {
                    Pal.Invariant(entries != null && _buckets != null && _comparer == comparer);
                    Pal.Invariant(0 <= _freeCount && _freeCount <= _count && _count <= entries.Length && _buckets.Length == entries.Length);
                    Pal.Invariant(typeof(T).IsValueType || _comparer != null);
                    Pal.Invariant(collisionCount <= (uint)entries.Length);
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), SearchLast(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, item, i, collisionCount, last)));
                    Pal.Invariant(Pal.Implies(!Pal.Returned(), ItemsOf(Pal.Contents(entries), _count) == items0.Value));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && Mem(_comparer, items0.Value, item) && Removed(_comparer, items0.Value, ItemsOf(Pal.Contents(entries), _count), item)));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Wf(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer) && _freeCount <= _count));
                    Pal.Invariant(entries.Length == length0.Value && entries.Length <= Array.MaxLength);
                    Pal.Decreases(length0.Value - collisionCount);
                    ref Entry entry = ref entries[i];

                    if (entry.HashCode == hashCode && (comparer?.Equals(entry.Value, item) ?? EqualityComparer<T>.Default.Equals(entry.Value, item)))
                    {
                        SearchNext(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount, last);
                        Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                        Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
                        if (last < 0)
                        {
                            bucket = entry.Next + 1; // Value in buckets is 1-based
                        }
                        else
                        {
                            entries[last].Next = entry.Next;
                        }

                        Debug.Assert((StartOfFreeList - _freeList) < 0, "shouldn't underflow because max hashtable length is MaxPrimeArrayLength = 0x7FEFFFFD(2146435069) _freelist underflow threshold 2147483646");
                        entry.Next = StartOfFreeList - _freeList;

                        if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
                        {
                            entry.Value = default!;
                        }

                        RemoveOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount, last);
                        _freeList = i;
                        _freeCount++;
                        return true;
                    }

                    SearchLastStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount, last);
                    last = i;
                    i = entry.Next;

                    collisionCount++;
                    if (collisionCount > (uint)entries.Length)
                    {
                        // The chain of entries forms a loop; which means a concurrent update has happened.
                        // Break out of the loop and throw, rather than looping forever.
                        ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                    }
                }
                SearchLastAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, item, i, collisionCount, last);
            }

            return false;
        }

        /// <summary>Gets the number of elements that are contained in the set.</summary>
        [Ensures("Result == @this.SpecCount && Result >= 0")]
        public int Count => _count - _freeCount;

        /// <summary>
        /// Gets the total numbers of elements the internal data structure can hold without resizing.
        /// </summary>
        [Ensures("Result == @this.SpecCapacity")]
        public int Capacity => _entries?.Length ?? 0;

        [Ensures("!Result")]
        bool ICollection<T>.IsReadOnly => false;

        #endregion

        #region AlternateLookup

        /// <summary>
        /// Gets an instance of a type that may be used to perform operations on the current <see cref="HashSet{T}"/>
        /// using a <typeparamref name="TAlternate"/> instead of a <typeparamref name="T"/>.
        /// </summary>
        /// <typeparam name="TAlternate">The alternate type of instance for performing lookups.</typeparam>
        /// <returns>The created lookup instance.</returns>
        /// <exception cref="InvalidOperationException">The set's comparer is not compatible with <typeparamref name="TAlternate"/>.</exception>
        /// <remarks>
        /// The set must be using a comparer that implements <see cref="IAlternateEqualityComparer{TAlternate, T}"/> with
        /// <typeparamref name="TAlternate"/> and <typeparamref name="T"/>. If it doesn't, an exception will be thrown.
        /// </remarks>
        public AlternateLookup<TAlternate> GetAlternateLookup<TAlternate>()
            where TAlternate : allows ref struct
        {
            if (!AlternateLookup<TAlternate>.IsCompatibleItem(this))
            {
                ThrowHelper.ThrowInvalidOperationException(ExceptionResource.InvalidOperation_IncompatibleComparer);
            }

            return new AlternateLookup<TAlternate>(this);
        }

        /// <summary>
        /// Gets an instance of a type that may be used to perform operations on the current <see cref="HashSet{T}"/>
        /// using a <typeparamref name="TAlternate"/> instead of a <typeparamref name="T"/>.
        /// </summary>
        /// <typeparam name="TAlternate">The alternate type of instance for performing lookups.</typeparam>
        /// <param name="lookup">The created lookup instance when the method returns true, or a default instance that should not be used if the method returns false.</param>
        /// <returns>true if a lookup could be created; otherwise, false.</returns>
        /// <remarks>
        /// The set must be using a comparer that implements <see cref="IAlternateEqualityComparer{TAlternate, T}"/> with
        /// <typeparamref name="TAlternate"/> and <typeparamref name="T"/>. If it doesn't, the method returns false.
        /// </remarks>
        public bool TryGetAlternateLookup<TAlternate>(out AlternateLookup<TAlternate> lookup)
            where TAlternate : allows ref struct
        {
            if (AlternateLookup<TAlternate>.IsCompatibleItem(this))
            {
                lookup = new AlternateLookup<TAlternate>(this);
                return true;
            }

            lookup = default;
            return false;
        }

        /// <summary>
        /// Provides a type that may be used to perform operations on a <see cref="HashSet{T}"/>
        /// using a <typeparamref name="TAlternate"/> instead of a <typeparamref name="T"/>.
        /// </summary>
        /// <typeparam name="TAlternate">The alternate type of instance for performing lookups.</typeparam>
        public struct AlternateLookup<TAlternate> where TAlternate : allows ref struct
        {
            /// <summary>Initialize the instance. The set must have already been verified to have a compatible comparer.</summary>
            internal AlternateLookup(HashSet<T> set)
            {
                Debug.Assert(set is not null);
                Debug.Assert(IsCompatibleItem(set));
                Set = set;
            }

            /// <summary>Gets the <see cref="HashSet{T}"/> against which this instance performs operations.</summary>
            public HashSet<T> Set { get; }

            /// <summary>Checks whether the set has a comparer compatible with <typeparamref name="TAlternate"/>.</summary>
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            internal static bool IsCompatibleItem(HashSet<T> set)
            {
                Debug.Assert(set is not null);
                return set._comparer is IAlternateEqualityComparer<TAlternate, T>;
            }

            /// <summary>Gets the set's alternate comparer. The set must have already been verified as compatible.</summary>
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            internal static IAlternateEqualityComparer<TAlternate, T> GetAlternateComparer(HashSet<T> set)
            {
                Debug.Assert(IsCompatibleItem(set));
                return Unsafe.As<IAlternateEqualityComparer<TAlternate, T>>(set._comparer)!;
            }

            /// <summary>Adds the specified element to a set.</summary>
            /// <param name="item">The element to add to the set.</param>
            /// <returns>true if the element is added to the set; false if the element is already present.</returns>
            public bool Add(TAlternate item)
            {
                HashSet<T> set = Set;
                IAlternateEqualityComparer<TAlternate, T> comparer = GetAlternateComparer(set);

                if (set._buckets == null)
                {
                    set.Initialize(0);
                }
                Debug.Assert(set._buckets != null);

                Entry[]? entries = set._entries;
                Debug.Assert(entries != null, "expected entries to be non-null");

                int hashCode;

                uint collisionCount = 0;
                ref int bucket = ref Unsafe.NullRef<int>();

                Debug.Assert(comparer is not null);
                hashCode = comparer.GetHashCode(item);
                bucket = ref set.GetBucketRef(hashCode);
                int i = bucket - 1; // Value in _buckets is 1-based
                while ((uint)i < (uint)entries.Length)
                {
                    Pal.Invariant(collisionCount <= (uint)entries.Length);
                    Pal.Decreases((uint)entries.Length - collisionCount);
                    ref Entry entry = ref entries[i];
                    if (entry.HashCode == hashCode && comparer.Equals(item, entry.Value))
                    {
                        return false;
                    }
                    i = entry.Next;

                    collisionCount++;
                    if (collisionCount > (uint)entries.Length)
                    {
                        // The chain of entries forms a loop, which means a concurrent update has happened.
                        ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                    }
                }

                // Invoke comparer.Map before allocating space in the collection in order to avoid corrupting
                // the collection if the operation fails.
                T mappedItem = comparer.Create(item);

                int index;
                if (set._freeCount > 0)
                {
                    index = set._freeList;
                    set._freeCount--;
                    Debug.Assert((StartOfFreeList - entries[set._freeList].Next) >= -1, "shouldn't overflow because `next` cannot underflow");
                    set._freeList = StartOfFreeList - entries[set._freeList].Next;
                }
                else
                {
                    int count = set._count;
                    if (count == entries.Length)
                    {
                        set.Resize();
                        bucket = ref set.GetBucketRef(hashCode);
                    }
                    index = count;
                    set._count = count + 1;
                    entries = set._entries;
                }

                {
                    ref Entry entry = ref entries![index];
                    entry.HashCode = hashCode;
                    entry.Next = bucket - 1; // Value in _buckets is 1-based
                    entry.Value = mappedItem;
                    bucket = index + 1;
                    set._version++;
                }

                // Value types never rehash
                if (!typeof(T).IsValueType && collisionCount > HashHelpers.HashCollisionThreshold && comparer is NonRandomizedStringEqualityComparer)
                {
                    // If we hit the collision threshold we'll need to switch to the comparer which is using randomized string hashing
                    // i.e. EqualityComparer<string>.Default.
                    set.Resize(entries.Length, forceNewHashCodes: true);
                }

                return true;
            }

            /// <summary>Removes the specified element from a set.</summary>
            /// <param name="item">The element to remove.</param>
            /// <returns>true if the element is successfully found and removed; otherwise, false.</returns>
            public bool Remove(TAlternate item)
            {
                HashSet<T> set = Set;
                IAlternateEqualityComparer<TAlternate, T> comparer = GetAlternateComparer(set);

                if (set._buckets != null)
                {
                    Entry[]? entries = set._entries;
                    Debug.Assert(entries != null, "entries should be non-null");

                    uint collisionCount = 0;
                    int last = -1;

                    int hashCode = item is not null ? comparer.GetHashCode(item) : 0;

                    ref int bucket = ref set.GetBucketRef(hashCode);
                    int i = bucket - 1; // Value in buckets is 1-based

                    while ((uint)i < (uint)entries.Length)
                    {
                        Pal.Invariant(collisionCount <= (uint)entries.Length);
                        Pal.Decreases((uint)entries.Length - collisionCount);
                        ref Entry entry = ref entries[i];

                        if (entry.HashCode == hashCode && comparer.Equals(item, entry.Value))
                        {
                            if (last < 0)
                            {
                                bucket = entry.Next + 1; // Value in buckets is 1-based
                            }
                            else
                            {
                                entries[last].Next = entry.Next;
                            }

                            Debug.Assert((StartOfFreeList - set._freeList) < 0, "shouldn't underflow because max hashtable length is MaxPrimeArrayLength = 0x7FEFFFFD(2146435069) _freelist underflow threshold 2147483646");
                            entry.Next = StartOfFreeList - set._freeList;

                            if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
                            {
                                entry.Value = default!;
                            }

                            set._freeList = i;
                            set._freeCount++;
                            return true;
                        }

                        last = i;
                        i = entry.Next;

                        collisionCount++;
                        if (collisionCount > (uint)entries.Length)
                        {
                            // The chain of entries forms a loop; which means a concurrent update has happened.
                            // Break out of the loop and throw, rather than looping forever.
                            ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                        }
                    }
                }

                return false;
            }

            /// <summary>Determines whether a set contains the specified element.</summary>
            /// <param name="item">The element to locate in the set.</param>
            /// <returns>true if the set contains the specified element; otherwise, false.</returns>
            public bool Contains(TAlternate item) => !Unsafe.IsNullRef(in FindValue(item));

            /// <summary>Searches the set for a given value and returns the equal value it finds, if any.</summary>
            /// <param name="equalValue">The value to search for.</param>
            /// <param name="actualValue">The value from the set that the search found, or the default value of <typeparamref name="T"/> when the search yielded no match.</param>
            /// <returns>A value indicating whether the search was successful.</returns>
            public bool TryGetValue(TAlternate equalValue, [MaybeNullWhen(false)] out T actualValue)
            {
                ref readonly T value = ref FindValue(equalValue);
                if (!Unsafe.IsNullRef(in value))
                {
                    actualValue = value;
                    return true;
                }

                actualValue = default!;
                return false;
            }

            /// <summary>Finds the item in the set and returns a reference to the found item, or a null reference if not found.</summary>
            internal ref readonly T FindValue(TAlternate item)
            {
                HashSet<T> set = Set;
                IAlternateEqualityComparer<TAlternate, T> comparer = GetAlternateComparer(set);

                ref Entry entry = ref Unsafe.NullRef<Entry>();
                if (set._buckets != null)
                {
                    Debug.Assert(set._entries != null, "expected entries to be != null");

                    int hashCode = comparer.GetHashCode(item);
                    int i = set.GetBucketRef(hashCode);
                    Entry[]? entries = set._entries;
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
                        if (entry.HashCode == hashCode && comparer.Equals(item, entry.Value))
                        {
                            goto ReturnFound;
                        }

                        i = entry.Next;

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
                ref readonly T value = ref entry.Value;
            Return:
                return ref value;
            ReturnNotFound:
                value = ref Unsafe.NullRef<T>();
                goto Return;
            }
        }
        #endregion

        #region IEnumerable methods

        [Ensures("ReferenceEquals(Result._hashSet, @this) && Result._version == @this.SpecVersion && Result._index == 0")]
        [Ensures("@this.SpecSlots >= 0")]
        public Enumerator GetEnumerator() => new Enumerator(this);

        [Ensures("Pal.Implies(@this.SpecCount != 0, Pal.Exists((HashSet<T>.Enumerator e) => Pal.Boxes(Result, e) && " +
            "ReferenceEquals(e._hashSet, @this) && e._version == @this.SpecVersion && e._index == 0))")]
        IEnumerator<T> IEnumerable<T>.GetEnumerator() =>
            Count == 0 ? SZGenericArrayEnumerator<T>.Empty :
            GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<T>)this).GetEnumerator();

        #endregion

        #region ISerializable methods

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        [EditorBrowsable(EditorBrowsableState.Never)]
        public virtual void GetObjectData(SerializationInfo info, StreamingContext context)
        {
            if (info == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.info);
            }

            info.AddValue(VersionName, _version); // need to serialize version to avoid problems with serializing while enumerating
            info.AddValue(ComparerName, Comparer, typeof(IEqualityComparer<T>));
            info.AddValue(CapacityName, _buckets == null ? 0 : _buckets.Length);

            if (_buckets != null)
            {
                var array = new T[Count];
                CopyTo(array);
                info.AddValue(ElementsName, array, typeof(T[]));
            }
        }

        #endregion

        #region IDeserializationCallback methods

        public virtual void OnDeserialization(object? sender)
        {
            HashHelpers.SerializationInfoTable.TryGetValue(this, out SerializationInfo? siInfo);
            if (siInfo == null)
            {
                // It might be necessary to call OnDeserialization from a container if the
                // container object also implements OnDeserialization. We can return immediately
                // if this function is called twice. Note we set _siInfo to null at the end of this method.
                return;
            }

            int capacity = siInfo.GetInt32(CapacityName);
            _comparer = (IEqualityComparer<T>)siInfo.GetValue(ComparerName, typeof(IEqualityComparer<T>))!;
            _freeList = -1;
            _freeCount = 0;

            if (capacity != 0)
            {
                _buckets = new int[capacity];
                _entries = new Entry[capacity];
#if TARGET_64BIT
                _fastModMultiplier = HashHelpers.GetFastModMultiplier((uint)capacity);
#endif

                T[]? array = (T[]?)siInfo.GetValue(ElementsName, typeof(T[]));
                if (array == null)
                {
                    ThrowHelper.ThrowSerializationException(ExceptionResource.Serialization_MissingKeys);
                }

                // There are no resizes here because we already set capacity above.
                for (int i = 0; i < array.Length; i++)
                {
                    AddIfNotPresent(array[i], out _);
                }
            }
            else
            {
                _buckets = null;
            }

            _version = siInfo.GetInt32(VersionName);
            HashHelpers.SerializationInfoTable.Remove(this);
        }

        #endregion

        #region HashSet methods

        /// <summary>Adds the specified element to the <see cref="HashSet{T}"/>.</summary>
        /// <param name="item">The element to add to the set.</param>
        /// <returns>true if the element is added to the <see cref="HashSet{T}"/> object; false if the element is already present.</returns>
        [Requires("@this.SpecSlots < 0x7FFFFFC3")]
        [Ensures("Implies(Result, HashSet<T>.Added(Old(@this.SpecItems), @this.SpecItems, item) && @this.SpecCount == Old(@this.SpecCount) + 1)")]
        [Ensures("Implies(Result, !HashSet<T>.Mem(Old(@this.SpecComparer), Old(@this.SpecItems), item))")]
        [Ensures("Implies(!Result, @this.SpecItems == Old(@this.SpecItems) && @this.SpecCount == Old(@this.SpecCount))")]
        [Ensures("Implies(!Result, HashSet<T>.Mem(@this.SpecComparer, @this.SpecItems, item))")]
        [Ensures("HashSet<T>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        public bool Add(T item) => AddIfNotPresent(item, out _);

        /// <summary>Searches the set for a given value and returns the equal value it finds, if any.</summary>
        /// <param name="equalValue">The value to search for.</param>
        /// <param name="actualValue">The value from the set that the search found, or the default value of <typeparamref name="T"/> when the search yielded no match.</param>
        /// <returns>A value indicating whether the search was successful.</returns>
        /// <remarks>
        /// This can be useful when you want to reuse a previously stored reference instead of
        /// a newly constructed one (so that more sharing of references can occur) or to look up
        /// a value that has more complete data than the value you currently have, although their
        /// comparer functions indicate they are equal.
        /// </remarks>
        [Ensures("Result == HashSet<T>.Mem(@this.SpecComparer, @this.SpecItems, equalValue)")]
        [Ensures("@this.SpecItems == Old(@this.SpecItems) && @this.SpecCount == Old(@this.SpecCount) && @this.SpecComparer == Old(@this.SpecComparer)")]
        public bool TryGetValue(T equalValue, [MaybeNullWhen(false)] out T actualValue)
        {
            if (_buckets != null)
            {
                int index = FindItemIndex(equalValue);
                if (index >= 0)
                {
                    actualValue = _entries![index].Value;
                    return true;
                }
            }

            actualValue = default;
            return false;
        }

        /// <summary>Modifies the current <see cref="HashSet{T}"/> object to contain all elements that are present in itself, the specified collection, or both.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        public void UnionWith(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // If this set is empty and other is a HashSet with the same effective comparer,
            // we can copy the data directly instead of adding each element individually.
            if (Count == 0 && other is HashSet<T> otherAsSet && EffectiveEqualityComparersAreEqual(this, otherAsSet))
            {
                ConstructFrom(otherAsSet);
                return;
            }

            foreach (T item in other)
            {
                AddIfNotPresent(item, out _);
            }
        }

        /// <summary>Modifies the current <see cref="HashSet{T}"/> object to contain only elements that are present in that object and in the specified collection.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        public void IntersectWith(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // Intersection of anything with empty set is empty set, so return if count is 0.
            // Same if the set intersecting with itself is the same set.
            if (Count == 0 || other == this)
            {
                return;
            }

            // If other is known to be empty, intersection is empty set; remove all elements, and we're done.
            if (other is ICollection<T> otherAsCollection)
            {
                if (otherAsCollection.Count == 0)
                {
                    Clear();
                    return;
                }

                // Faster if other is a hashset using same equality comparer; so check
                // that other is a hashset using the same equality comparer.
                if (other is HashSet<T> otherAsSet && EqualityComparersAreEqual(this, otherAsSet))
                {
                    IntersectWithHashSetWithSameComparer(otherAsSet);
                    return;
                }
            }

            IntersectWithEnumerable(other);
        }

        /// <summary>Removes all elements in the specified collection from the current <see cref="HashSet{T}"/> object.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        [Ensures("@this.SpecComparer == Old(@this.SpecComparer)")]
        [Ensures("Pal.Implies(HashSet<T>.Equiv(@this.SpecComparer) && HashSet<T>.Distinct(@this.SpecComparer, Old(@this.SpecItems)), " +
            "HashSet<T>.Distinct(@this.SpecComparer, @this.SpecItems) && HashSet<T>.Except(@this.SpecComparer, Old(@this.SpecItems), Pal.Contents(other), @this.SpecItems))")]
        [OpaqueSpecs("Except", "Distinct", "Equiv")]
        public void ExceptWith(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // This is already the empty set; return.
            if (Count == 0)
            {
                ItemsCount(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, _comparer);
                ExceptEmpty(_comparer, this.SpecItems, Pal.Contents(other));
                return;
            }

            // Special case if other is this; a set minus itself is the empty set.
            if (other == this)
            {
                Clear();
                return;
            }

            // Remove every element in other from this.
            Ghost<Seq<T>> items0 = this.SpecItems;
            ExceptStart(_comparer, this.SpecItems, Pal.Contents(other));
            foreach (T element in other)
            {
                Pal.Invariant(0 <= _freeCount && _freeCount <= _count && _count <= _entries.Length);
                Pal.Invariant((_buckets == null) == (_entries == null) && _buckets.Length == _entries.Length);
                Pal.Invariant((_entries != null || _count == 0) && (_entries != null || _entries.Length == 0));
                Pal.Invariant(_entries == null || (_entries.Length > 0 && _entries.Length <= Array.MaxLength && System.Collections.HashHelpers.PrimeSize(_entries.Length)));
                Pal.Invariant(typeof(T).IsValueType || _comparer != null);
                Pal.Invariant(_buckets == null || HashSet<T>.Wf(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, _comparer));
                Pal.Invariant(_comparer == Pal.Old(this.SpecComparer) &&
                              0 <= Pal.Index(element) && Pal.Index(element) <= Pal.Contents(other).Length &&
                              Pal.Implies(HashSet<T>.Equiv(_comparer) && HashSet<T>.Distinct(_comparer, items0.Value),
                                  HashSet<T>.Distinct(_comparer, ItemsOf(Pal.Contents(_entries), _count)) &&
                                  HashSet<T>.Except(_comparer, items0.Value, Pal.Slice(Pal.Contents(other), 0, Pal.Index(element)),
                                      ItemsOf(Pal.Contents(_entries), _count))));
                Ghost<Seq<T>> before = ItemsOf(Pal.Contents(_entries), _count);
                Remove(element);
                ExceptStep(_comparer, items0.Value, Pal.Contents(other), before.Value, ItemsOf(Pal.Contents(_entries), _count), Pal.Index(element) - 1);
            }
            ExceptDone(_comparer, items0.Value, Pal.Contents(other), ItemsOf(Pal.Contents(_entries), _count));
        }

        /// <summary>Modifies the current <see cref="HashSet{T}"/> object to contain only elements that are present either in that object or in the specified collection, but not both.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        public void SymmetricExceptWith(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // If set is empty, then symmetric difference is other.
            if (Count == 0)
            {
                UnionWith(other);
                return;
            }

            // Special-case this; the symmetric difference of a set with itself is the empty set.
            if (other == this)
            {
                Clear();
                return;
            }

            // If other is a HashSet, it has unique elements according to its equality comparer,
            // but if they're using different equality comparers, then assumption of uniqueness
            // will fail. So first check if other is a hashset using the same equality comparer;
            // symmetric except is a lot faster and avoids bit array allocations if we can assume
            // uniqueness.
            if (other is HashSet<T> otherAsSet && EqualityComparersAreEqual(this, otherAsSet))
            {
                SymmetricExceptWithUniqueHashSet(otherAsSet);
            }
            else
            {
                SymmetricExceptWithEnumerable(other);
            }
        }

        /// <summary>Determines whether a <see cref="HashSet{T}"/> object is a subset of the specified collection.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        /// <returns>true if the <see cref="HashSet{T}"/> object is a subset of <paramref name="other"/>; otherwise, false.</returns>
        public bool IsSubsetOf(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // The empty set is a subset of any set, and a set is a subset of itself.
            // Set is always a subset of itself.
            if (Count == 0 || other == this)
            {
                return true;
            }

            if (other is ICollection<T> otherAsCollection)
            {
                // If this has more elements then it can't be a subset.
                if (Count > otherAsCollection.Count)
                {
                    return false;
                }

                // Faster if other has unique elements according to this equality comparer; so check
                // that other is a hashset using the same equality comparer.
                if (other is HashSet<T> otherAsSet && EqualityComparersAreEqual(this, otherAsSet))
                {
                    return IsSubsetOfHashSetWithSameComparer(otherAsSet);
                }
            }

            (int uniqueCount, int unfoundCount) = CheckUniqueAndUnfoundElements(other, returnIfUnfound: false);
            return uniqueCount == Count && unfoundCount >= 0;
        }

        /// <summary>Determines whether a <see cref="HashSet{T}"/> object is a proper subset of the specified collection.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        /// <returns>true if the <see cref="HashSet{T}"/> object is a proper subset of <paramref name="other"/>; otherwise, false.</returns>
        public bool IsProperSubsetOf(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // No set is a proper subset of itself.
            if (other == this)
            {
                return false;
            }

            if (other is ICollection<T> otherAsCollection)
            {
                // No set is a proper subset of a set with less or equal number of elements.
                if (otherAsCollection.Count <= Count)
                {
                    return false;
                }

                // The empty set is a proper subset of anything but the empty set.
                if (Count == 0)
                {
                    // Based on check above, other is not empty when Count == 0.
                    return true;
                }

                // Faster if other is a hashset (and we're using same equality comparer).
                if (other is HashSet<T> otherAsSet && EqualityComparersAreEqual(this, otherAsSet))
                {
                    // This has strictly less than number of items in other, so the following
                    // check suffices for proper subset.
                    return IsSubsetOfHashSetWithSameComparer(otherAsSet);
                }
            }

            (int uniqueCount, int unfoundCount) = CheckUniqueAndUnfoundElements(other, returnIfUnfound: false);
            return uniqueCount == Count && unfoundCount > 0;
        }

        /// <summary>Determines whether a <see cref="HashSet{T}"/> object is a proper superset of the specified collection.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        /// <returns>true if the <see cref="HashSet{T}"/> object is a superset of <paramref name="other"/>; otherwise, false.</returns>
        public bool IsSupersetOf(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // A set is always a superset of itself.
            if (other == this)
            {
                return true;
            }

            // Try to fall out early based on counts.
            if (other is ICollection<T> otherAsCollection)
            {
                // If other is the empty set then this is a superset.
                if (otherAsCollection.Count == 0)
                {
                    return true;
                }

                // Try to compare based on counts alone if other is a hashset with same equality comparer.
                if (other is HashSet<T> otherAsSet &&
                    EqualityComparersAreEqual(this, otherAsSet) &&
                    otherAsSet.Count > Count)
                {
                    return false;
                }
            }

            foreach (T element in other)
            {
                if (!Contains(element))
                {
                    return false;
                }
            }

            return true;
        }

        /// <summary>Determines whether a <see cref="HashSet{T}"/> object is a proper superset of the specified collection.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        /// <returns>true if the <see cref="HashSet{T}"/> object is a proper superset of <paramref name="other"/>; otherwise, false.</returns>
        public bool IsProperSupersetOf(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // The empty set isn't a proper superset of any set, and a set is never a strict superset of itself.
            if (Count == 0 || other == this)
            {
                return false;
            }

            if (other is ICollection<T> otherAsCollection)
            {
                // If other is the empty set then this is a superset.
                if (otherAsCollection.Count == 0)
                {
                    // Note that this has at least one element, based on above check.
                    return true;
                }

                // Faster if other is a hashset with the same equality comparer
                if (other is HashSet<T> otherAsSet && EqualityComparersAreEqual(this, otherAsSet))
                {
                    if (otherAsSet.Count >= Count)
                    {
                        return false;
                    }

                    // Now perform element check.
                    return otherAsSet.IsSubsetOfHashSetWithSameComparer(this);
                }
            }

            // Couldn't fall out in the above cases; do it the long way
            (int uniqueCount, int unfoundCount) = CheckUniqueAndUnfoundElements(other, returnIfUnfound: true);
            return uniqueCount < Count && unfoundCount == 0;
        }

        /// <summary>Determines whether the current <see cref="HashSet{T}"/> object and a specified collection share common elements.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        /// <returns>true if the <see cref="HashSet{T}"/> object and <paramref name="other"/> share at least one common element; otherwise, false.</returns>
        public bool Overlaps(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            if (Count == 0)
            {
                return false;
            }

            // Set overlaps itself
            if (other == this)
            {
                return true;
            }

            // Fast path for Overlaps when other is HashSet with same equality comparer
            if (other is HashSet<T> otherAsSet && EqualityComparersAreEqual(this, otherAsSet))
            {
                return otherAsSet.Count > Count ? OverlapsHashSetImpl(this, otherAsSet) : OverlapsHashSetImpl(otherAsSet, this);
            }

            return OverlapsEnumerableImpl(other);
        }

        [Ensures("Pal.Implies(Result, HashSet<T>.OverlapsSeq(@this.SpecComparer, @this.SpecItems, Pal.Contents(other)))")]
        [Ensures("Pal.Implies(!Result, !HashSet<T>.OverlapsSeq(@this.SpecComparer, @this.SpecItems, Pal.Contents(other)))")]
        private bool OverlapsEnumerableImpl(IEnumerable<T> other)
        {
            foreach (T element in other)
            {
                Pal.Invariant(0 <= Pal.Index(element) && Pal.Index(element) <= Pal.Contents(other).Length &&
                              (Pal.Returned()
                                  ? Pal.ReturnValue<bool>() && HashSet<T>.OverlapsSeq(this.SpecComparer, this.SpecItems, Pal.Contents(other))
                                  : HashSet<T>.NoOverlap(this.SpecComparer, this.SpecItems, Pal.Contents(other), Pal.Index(element))));
                if (Contains(element))
                {
                    OverlapsHit(this.SpecComparer, this.SpecItems, Pal.Contents(other), Pal.Index(element) - 1);
                    return true;
                }
                NoOverlapStep(this.SpecComparer, this.SpecItems, Pal.Contents(other), Pal.Index(element) - 1);
            }

            NoOverlapDone(this.SpecComparer, this.SpecItems, Pal.Contents(other));
            return false;
        }

        // R30.41. A static walk over `smaller`'s prefixes, as in `IsSubsetOfHashSetWithSameComparer`.
        [Ensures("Pal.Implies(Result, HashSet<T>.OverlapsSeq(larger.SpecComparer, larger.SpecItems, smaller.SpecItems))")]
        [Ensures("Pal.Implies(!Result, !HashSet<T>.OverlapsSeq(larger.SpecComparer, larger.SpecItems, smaller.SpecItems))")]
        private static bool OverlapsHashSetImpl(HashSet<T> smaller, HashSet<T> larger)
        {
            foreach (T element in smaller)
            {
                Pal.Invariant(Pal.Enumerator<Enumerator>(element).SpecFresh &&
                              0 <= Pal.Enumerator<Enumerator>(element).SpecIndex &&
                              Pal.Enumerator<Enumerator>(element).SpecIndex <= smaller.SpecSlots &&
                              (Pal.Returned()
                                  ? Pal.ReturnValue<bool>() && HashSet<T>.OverlapsSeq(larger.SpecComparer, larger.SpecItems, smaller.SpecItems)
                                  : Pal.Implies(Pal.Enumerator<Enumerator>(element).SpecIndex != 0,
                                        smaller.SpecPrefixes.Length == smaller.SpecSlots + 1 &&
                                        HashSet<T>.NoneIn(larger.SpecComparer, larger.SpecItems,
                                            smaller.SpecPrefixes[Pal.Enumerator<Enumerator>(element).SpecIndex]))));
                Pal.Decreases(smaller.SpecSlots - Pal.Enumerator<Enumerator>(element).SpecIndex);
                if (larger.Contains(element))
                {
                    OverlapsWalk(larger.SpecComparer, larger.SpecItems, smaller.SpecPrefixes, smaller.SpecItems,
                        Pal.Enumerator<Enumerator>(element).SpecIndex);
                    return true;
                }
            }

            NoneInWalk(larger.SpecComparer, larger.SpecItems, smaller.SpecPrefixes, smaller.SpecItems);
            return false;
        }

        /// <summary>Determines whether a <see cref="HashSet{T}"/> object and the specified collection contain the same elements.</summary>
        /// <param name="other">The collection to compare to the current <see cref="HashSet{T}"/> object.</param>
        /// <returns>true if the <see cref="HashSet{T}"/> object is equal to <paramref name="other"/>; otherwise, false.</returns>
        public bool SetEquals(IEnumerable<T> other)
        {
            if (other == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.other);
            }

            // A set is equal to itself.
            if (other == this)
            {
                return true;
            }

            if (other is ICollection<T> otherAsCollection)
            {
                // If this is empty, they are equal iff other is empty.
                if (Count == 0)
                {
                    return otherAsCollection.Count == 0;
                }

                // Faster if other is a hashset and we're using same equality comparer.
                if (other is HashSet<T> otherAsSet && EqualityComparersAreEqual(this, otherAsSet))
                {
                    // Attempt to return early: since both contain unique elements, if they have
                    // different counts, then they can't be equal.
                    if (Count != otherAsSet.Count)
                    {
                        return false;
                    }

                    // Already confirmed that the sets have the same number of distinct elements, so if
                    // one is a subset of the other then they must be equal.
                    return IsSubsetOfHashSetWithSameComparer(otherAsSet);
                }

                // Can't be equal if other set contains fewer elements than this.
                if (Count > otherAsCollection.Count)
                {
                    return false;
                }
            }

            (int uniqueCount, int unfoundCount) = CheckUniqueAndUnfoundElements(other, returnIfUnfound: true);
            return uniqueCount == Count && unfoundCount == 0;
        }

        [Requires("array != null")]
        [Throws(typeof(ArgumentException), "@this.SpecCount > Pal.Contents(array).Length")]
        [Ensures("@this.SpecItems == Pal.Old(@this.SpecItems) && @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecVersion == Pal.Old(@this.SpecVersion)")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("@this.SpecItems.Length == @this.SpecCount")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), 0, @this.SpecItems.Length, @this.SpecItems)")]
        public void CopyTo(T[] array) => CopyTo(array, 0, Count);

        /// <summary>Copies the elements of a <see cref="HashSet{T}"/> object to an array, starting at the specified array index.</summary>
        /// <param name="array">The destination array.</param>
        /// <param name="arrayIndex">The zero-based index in array at which copying begins.</param>
        [Requires("array != null && arrayIndex >= 0")]
        [Throws(typeof(ArgumentException), "arrayIndex > Pal.Contents(array).Length || @this.SpecCount > Pal.Contents(array).Length - arrayIndex")]
        [Ensures("@this.SpecItems == Pal.Old(@this.SpecItems) && @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecVersion == Pal.Old(@this.SpecVersion)")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("@this.SpecItems.Length == @this.SpecCount")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), arrayIndex, arrayIndex + @this.SpecItems.Length, @this.SpecItems)")]
        public void CopyTo(T[] array, int arrayIndex) => CopyTo(array, arrayIndex, Count);

        [Requires("array != null && arrayIndex >= 0 && count >= 0")]
        [Throws(typeof(ArgumentException), "arrayIndex > Pal.Contents(array).Length || count > Pal.Contents(array).Length - arrayIndex")]
        [Ensures("@this.SpecItems == Pal.Old(@this.SpecItems) && @this.SpecCount == Pal.Old(@this.SpecCount) && @this.SpecVersion == Pal.Old(@this.SpecVersion)")]
        [Ensures("@this.SpecItems.Length == @this.SpecCount")]
        [Ensures("Pal.Contents(array).Length == Pal.Old(Pal.Contents(array)).Length")]
        [Ensures("Pal.Implies(count <= @this.SpecItems.Length, Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), arrayIndex, arrayIndex + count, Pal.Slice(@this.SpecItems, 0, count)))")]
        [Ensures("Pal.Implies(@this.SpecItems.Length < count, Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), arrayIndex, arrayIndex + @this.SpecItems.Length, @this.SpecItems))")]
        public void CopyTo(T[] array, int arrayIndex, int count)
        {
            if (array == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.array);
            }

            ArgumentOutOfRangeException.ThrowIfNegative(arrayIndex);
            ArgumentOutOfRangeException.ThrowIfNegative(count);

            // Will the array, starting at arrayIndex, be able to hold elements? Note: not
            // checking arrayIndex >= array.Length (consistency with list of allowing
            // count of 0; subsequent check takes care of the rest)
            if (arrayIndex > array.Length || count > array.Length - arrayIndex)
            {
                ThrowHelper.ThrowArgumentException(ExceptionResource.Arg_ArrayPlusOffTooSmall);
            }

            ItemsCount(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, _comparer);
            Entry[]? entries = _entries;
            Ghost<Seq<T>> array0 = Pal.Contents(array);
            Ghost<int> arrayIndex0 = arrayIndex;
            Ghost<int> count0 = count;
            for (int i = 0; i < _count && count != 0; i++)
            {
                Pal.Invariant(0 <= i && i <= _count && (entries != null || _count == 0));
                Pal.Invariant(arrayIndex == arrayIndex0.Value + ItemsOf(Pal.Contents(entries), i).Length);
                Pal.Invariant(count == count0.Value - ItemsOf(Pal.Contents(entries), i).Length);
                Pal.Invariant(count >= 0 && arrayIndex0.Value + count0.Value <= array0.Value.Length);
                Pal.Invariant(Pal.Contents(array).Length == array0.Value.Length);
                Pal.Invariant(Pal.Contents(array) == Pal.Splice(array0.Value, arrayIndex0.Value, arrayIndex, ItemsOf(Pal.Contents(entries), i)));
                Pal.Invariant(ItemsOf(Pal.Contents(entries), i).Length <= ItemsOf(Pal.Contents(entries), _count).Length);
                Pal.Invariant(ItemsOf(Pal.Contents(entries), i) == Pal.Slice(ItemsOf(Pal.Contents(entries), _count), 0, ItemsOf(Pal.Contents(entries), i).Length));
                ItemsStep(Pal.Contents(entries), i);
                ref Entry entry = ref entries![i];
                if (entry.Next >= -1)
                {
                    array[arrayIndex++] = entry.Value;
                    count--;
                }
                ItemsPrefix(Pal.Contents(entries), i + 1, _count);
            }
        }

        /// <summary>Removes all elements that match the conditions defined by the specified predicate from a <see cref="HashSet{T}"/> collection.</summary>
        [Ensures("@this.SpecComparer == Old(@this.SpecComparer)")]
        [Throws(typeof(ArgumentNullException), "match == null")]
        [Ensures("0 <= Result && Result == Old(@this.SpecItems).Length - @this.SpecItems.Length")]
        [Ensures("Pal.Implies(HashSet<T>.Equiv(@this.SpecComparer) && HashSet<T>.Distinct(@this.SpecComparer, Old(@this.SpecItems)), " +
            "HashSet<T>.Distinct(@this.SpecComparer, @this.SpecItems) && HashSet<T>.AllIn(@this.SpecComparer, Old(@this.SpecItems), @this.SpecItems))")]
        [OpaqueSpecs("Distinct", "Equiv", "AllIn")]
        public int RemoveWhere(Predicate<T> match)
        {
            if (match == null)
            {
                ThrowHelper.ThrowArgumentNullException(ExceptionArgument.match);
            }

            Entry[]? entries = _entries;
            int numRemoved = 0;
            ItemsCount(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, _comparer);
            Ghost<Seq<T>> items0 = this.SpecItems;
            AllInRefl(_comparer, items0.Value);
            for (int i = 0; i < _count; i++)
            {
                Pal.Invariant(0 <= _freeCount && _freeCount <= _count && _count <= _entries.Length);
                Pal.Invariant((_buckets == null) == (_entries == null) && _buckets.Length == _entries.Length);
                Pal.Invariant((_entries != null || _count == 0) && (_entries != null || _entries.Length == 0));
                Pal.Invariant(_entries == null || (_entries.Length > 0 && _entries.Length <= Array.MaxLength && System.Collections.HashHelpers.PrimeSize(_entries.Length)));
                Pal.Invariant(typeof(T).IsValueType || _comparer != null);
                Pal.Invariant(_buckets == null || HashSet<T>.Wf(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, _comparer));
                Pal.Invariant(0 <= i && Pal.Old(this.SpecItems).Length <= Array.MaxLength);
                Pal.Invariant(_comparer == Pal.Old(this.SpecComparer));
                Pal.Invariant(0 <= numRemoved && numRemoved == Pal.Old(this.SpecItems).Length - ItemsOf(Pal.Contents(_entries), _count).Length);
                Pal.Invariant(Pal.Implies(HashSet<T>.Equiv(_comparer) && HashSet<T>.Distinct(_comparer, items0.Value),
                    HashSet<T>.Distinct(_comparer, ItemsOf(Pal.Contents(_entries), _count)) &&
                    HashSet<T>.AllIn(_comparer, items0.Value, ItemsOf(Pal.Contents(_entries), _count))));
                ref Entry entry = ref entries![i];
                if (entry.Next >= -1)
                {
                    // Cache value in case delegate removes it
                    T value = entry.Value;
                    if (match(value))
                    {
                        Ghost<Seq<T>> before = ItemsOf(Pal.Contents(_entries), _count);
                        // Check again that remove actually removed it.
                        if (Remove(value))
                        {
                            numRemoved++;
                        }
                        RemoveWhereStep(_comparer, items0.Value, before.Value, ItemsOf(Pal.Contents(_entries), _count), value);
                    }
                }
            }

            return numRemoved;
        }

        /// <summary>Gets the <see cref="IEqualityComparer"/> object that is used to determine equality for the values in the set.</summary>
        [Ensures("HashSet<T>.SameEquality(Result, @this.SpecComparer)")]
        public IEqualityComparer<T> Comparer
        {
            get
            {
                if (typeof(T) == typeof(string))
                {
                    Debug.Assert(_comparer is not null, "The comparer should never be null for a reference type.");
                    return (IEqualityComparer<T>)IInternalStringEqualityComparer.GetUnderlyingEqualityComparer((IEqualityComparer<string?>)_comparer);
                }
                else
                {
                    return _comparer ?? EqualityComparer<T>.Default;
                }
            }
        }

        /// <summary>
        /// Similar to <see cref="Comparer"/> but surfaces the actual comparer being used to hash entries.
        /// </summary>
        [Ensures("HashSet<T>.SameEquality(Result, @this.SpecComparer)")]
        internal IEqualityComparer<T> EffectiveComparer => _comparer ?? EqualityComparer<T>.Default;

        /// <summary>Ensures that this hash set can hold the specified number of elements without growing.</summary>
        [Requires("capacity <= 0x7FFFFFC3")]
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
        [Ensures("capacity <= Result && Result == @this.SpecCapacity")]
        [Ensures("@this.SpecItems == Old(@this.SpecItems) && @this.SpecCount == Old(@this.SpecCount) && @this.SpecComparer == Old(@this.SpecComparer)")]
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

            if (_buckets == null)
            {
                return Initialize(capacity);
            }

            int newSize = HashHelpers.GetPrime(capacity);
            Resize(newSize, forceNewHashCodes: false);
            return newSize;
        }

        [Requires("0 < @this.SpecCapacity && @this.SpecCapacity <= @this.SpecSlots && @this.SpecSlots < 0x7FFFFFC3")]
        [Ensures("@this.SpecCapacity > Old(@this.SpecSlots) && @this.SpecSlots == Old(@this.SpecSlots) && @this.SpecCount == Old(@this.SpecCount)")]
        [Ensures("@this.SpecItems == Old(@this.SpecItems) && @this.SpecVersion == Old(@this.SpecVersion) && @this.SpecComparer == Old(@this.SpecComparer)")]
        private void Resize() => Resize(HashHelpers.ExpandPrime(_count), forceNewHashCodes: false);

        [Requires("Pal.Implies(forceNewHashCodes, !typeof(T).IsValueType && HashSet<T>.NonRandomized(@this.SpecComparer))")]
        [Requires("0 < @this.SpecCapacity && @this.SpecCapacity <= newSize && newSize <= 0x7FFFFFC7 && System.Collections.HashHelpers.PrimeSize(newSize)")]
        [Ensures("@this.SpecCapacity == newSize && @this.SpecSlots == Old(@this.SpecSlots) && @this.SpecCount == Old(@this.SpecCount)")]
        [Ensures("@this.SpecItems == Old(@this.SpecItems) && @this.SpecVersion == Old(@this.SpecVersion)")]
        [Ensures("Pal.Implies(!forceNewHashCodes, @this.SpecComparer == Old(@this.SpecComparer))")]
        [Ensures("HashSet<T>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        private void Resize(int newSize, bool forceNewHashCodes)
        {
            // Value types never rehash
            Debug.Assert(!forceNewHashCodes || !typeof(T).IsValueType);
            Debug.Assert(_entries != null, "_entries should be non-null");
            Debug.Assert(HashHelpers.IsPrime(newSize));
            Debug.Assert(newSize >= _entries.Length);

            var entries = new Entry[newSize];

            int count = _count;
            Ghost<Seq<Entry>> old0 = Pal.Contents(_entries);
            Array.Copy(_entries, entries, count);
            CopyOk(Pal.Contents(_buckets), old0.Value, Pal.Contents(entries), count, _freeList, _freeCount, _comparer);

            if (!typeof(T).IsValueType && forceNewHashCodes)
            {
                Debug.Assert(_comparer is NonRandomizedStringEqualityComparer);
                RandomizedSame(_comparer);
                PreFreeOf(Pal.Contents(entries), count, _freeList, _freeCount, _comparer);
                Ghost<Seq<Entry>> copied = Pal.Contents(entries);
                IEqualityComparer<T> comparer = _comparer = (IEqualityComparer<T>)((NonRandomizedStringEqualityComparer)_comparer).GetRandomizedEqualityComparer();

                RehashStart(copied.Value, count, _comparer);
                for (int i = 0; i < count; i++)
                {
                    Pal.Invariant(0 <= i && entries.Length == newSize && Holds(_comparer, comparer));
                    Pal.Invariant(HashSet<T>.Rehashed(copied.Value, Pal.Contents(entries), count, i, _comparer));
                    Ghost<Seq<Entry>> before = Pal.Contents(entries);
                    ref Entry entry = ref entries[i];
                    if (entry.Next >= -1)
                    {
                        entry.HashCode = entry.Value != null ? comparer.GetHashCode(entry.Value) : 0;
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
                ref Entry entry = ref entries[i];
                Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
                if (entry.Next >= -1)
                {
                    RebuildBucket(Pal.Contents(_buckets), source.Value, Pal.Contents(entries), count, i);
                    ref int bucket = ref GetBucketRef(entry.HashCode);
                    entry.Next = bucket - 1; // Value in _buckets is 1-based
                    bucket = i + 1;
                }
                RebuildStep(buckets0.Value, Pal.Contents(_buckets), source.Value, entries0.Value, Pal.Contents(entries), count, i);
            }

            _entries = entries;
            RebuildDone(Pal.Contents(_buckets), source.Value, Pal.Contents(_entries), count, _freeList, _freeCount, _comparer);
        }

        // [Open] (R27.23): `TrimExcess` calls it with the new, empty arrays in place and the old
        // entries in hand, where the invariant does not hold.
        [Open]
        [Requires("@this._entries != null && @this._buckets != null && 0 <= count && count <= entries.Length && @this._freeList == -1")]
        [Requires("Pal.Contents(@this._entries).Length > 0 && Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length && HashSet<T>.Zeros(Pal.Contents(@this._buckets))")]
        [Requires("HashSet<T>.Compactable(Pal.Contents(entries), count, @this._comparer) && HashSet<T>.ItemsOf(Pal.Contents(entries), count).Length <= Pal.Contents(@this._entries).Length")]
        [Ensures("@this._entries != null && @this._buckets != null && @this._freeList == -1 && @this._freeCount == 0")]
        [Ensures("Pal.Contents(@this._entries).Length == Old(Pal.Contents(@this._entries).Length) && Pal.Contents(@this._buckets).Length == Pal.Contents(@this._entries).Length")]
        [Ensures("@this._comparer == Old(@this._comparer) && @this._version == Old(@this._version)")]
        [Ensures("Pal.Contents(entries) == Old(Pal.Contents(entries)) && HashSet<T>.ItemsOf(Pal.Contents(@this._entries), @this._count).Length == @this._count")]
        [Ensures("HashSet<T>.Wf(Pal.Contents(@this._buckets), Pal.Contents(@this._entries), @this._count, @this._freeList, @this._freeCount, @this._comparer)")]
        [Ensures("HashSet<T>.ItemsOf(Pal.Contents(@this._entries), @this._count) == HashSet<T>.ItemsOf(Pal.Contents(entries), count)")]
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
                Pal.Invariant(HashSet<T>.Compacted(Pal.Contents(_buckets), Pal.Contents(entries), Pal.Contents(newEntries), count, i, newCount, _comparer));
                Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
                Ghost<Seq<Entry>> entries0 = Pal.Contents(newEntries);
                Ghost<int> m0 = newCount;
                int hashCode = entries[i].HashCode;
                if (entries[i].Next >= -1)
                {
                    CompactRoom(Pal.Contents(_buckets), Pal.Contents(entries), Pal.Contents(newEntries), count, i, newCount, _comparer);
                    ref Entry entry = ref newEntries[newCount];
                    entry = entries[i];
                    ref int bucket = ref GetBucketRef(hashCode);
                    entry.Next = bucket - 1; // Value in _buckets is 1-based
                    bucket = newCount + 1;
                    newCount++;
                }
                CompactStep(buckets0.Value, Pal.Contents(_buckets), Pal.Contents(entries), entries0.Value, Pal.Contents(newEntries), count, i, m0.Value, newCount, _comparer);
            }

            CompactDone(Pal.Contents(_buckets), Pal.Contents(entries), Pal.Contents(newEntries), count, newCount, _comparer);
            _count = newCount;
            _freeCount = 0;
        }

        /// <summary>
        /// Sets the capacity of a <see cref="HashSet{T}"/> object to the actual number of elements it contains,
        /// rounded up to a nearby, implementation-specific value.
        /// </summary>
        [Ensures("@this.SpecItems == Old(@this.SpecItems) && @this.SpecCount == Old(@this.SpecCount) && @this.SpecComparer == Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCapacity <= Old(@this.SpecCapacity)")]
        public void TrimExcess() => TrimExcess(Count);

        /// <summary>
        /// Sets the capacity of a <see cref="HashSet{T}"/> object to the specified number of entries,
        /// rounded up to a nearby, implementation-specific value.
        /// </summary>
        /// <param name="capacity">The new capacity.</param>
        /// <exception cref="ArgumentOutOfRangeException">Passed capacity is lower than entries count.</exception>
        [Throws(typeof(ArgumentOutOfRangeException), "capacity < @this.SpecCount")]
        [Ensures("@this.SpecItems == Old(@this.SpecItems) && @this.SpecCount == Old(@this.SpecCount) && @this.SpecComparer == Old(@this.SpecComparer)")]
        [Ensures("@this.SpecCapacity <= Old(@this.SpecCapacity)")]
        public void TrimExcess(int capacity)
        {
            ArgumentOutOfRangeException.ThrowIfLessThan(capacity, Count);

            int newSize = HashHelpers.GetPrimeAtLeast(capacity);
            Entry[]? oldEntries = _entries;
            if (oldEntries is null || newSize >= oldEntries.Length)
            {
                return;
            }

            _version++;

            Debug.Assert(HashHelpers.IsPrime(newSize));
            Debug.Assert(newSize >= Count);

            var buckets = new int[newSize];
            var entries = new Entry[newSize];

            WfCompactable(Pal.Contents(_buckets), Pal.Contents(oldEntries), _count, _freeList, _freeCount, _comparer);
            // Assign member variables after both arrays are allocated to guard against corruption from OOM if second fails.
            _freeList = -1;
            _buckets = buckets;
            _entries = entries;
#if TARGET_64BIT
            _fastModMultiplier = HashHelpers.GetFastModMultiplier((uint)newSize);
#endif

            CopyEntries(oldEntries, _count);
        }

        #endregion

        #region Helper methods

        /// <summary>Returns an <see cref="IEqualityComparer"/> object that can be used for equality testing of a <see cref="HashSet{T}"/> object.</summary>
        public static IEqualityComparer<HashSet<T>> CreateSetComparer() => new HashSetEqualityComparer<T>();

        /// <summary>
        /// Initializes buckets and slots arrays. Uses suggested capacity by finding next prime
        /// greater than or equal to capacity.
        /// </summary>
        [Requires("0 <= capacity && capacity <= 0x7FFFFFC3 && @this.SpecSlots == 0")]
        [Ensures("capacity <= Result && 0 < Result && Result == @this.SpecCapacity")]
        [Ensures("@this.SpecSlots == 0 && @this.SpecCount == 0 && @this.SpecItems == Pal.EmptySeq<T>()")]
        [Ensures("@this.SpecComparer == Old(@this.SpecComparer) && @this.SpecVersion == Old(@this.SpecVersion)")]
        private int Initialize(int capacity)
        {
            int size = HashHelpers.GetPrime(capacity);
            var buckets = new int[size];
            var entries = new Entry[size];
            WfFresh(Pal.Contents(buckets), Pal.Contents(entries), _comparer);

            // Assign member variables after both arrays are allocated to guard against corruption from OOM if second fails.
            _freeList = -1;
            _buckets = buckets;
            _entries = entries;
#if TARGET_64BIT
            _fastModMultiplier = HashHelpers.GetFastModMultiplier((uint)size);
#endif

            return size;
        }

        /// <summary>Adds the specified element to the set if it's not already contained.</summary>
        /// <param name="value">The element to add to the set.</param>
        /// <param name="location">The index into <see cref="_entries"/> of the element.</param>
        /// <returns>true if the element is added to the <see cref="HashSet{T}"/> object; false if the element is already present.</returns>
        [Requires("@this.SpecSlots < 0x7FFFFFC3")]
        [Ensures("Implies(Result, HashSet<T>.Added(Old(@this.SpecItems), @this.SpecItems, value) && @this.SpecCount == Old(@this.SpecCount) + 1)")]
        [Ensures("Implies(Result, !HashSet<T>.Mem(Old(@this.SpecComparer), Old(@this.SpecItems), value))")]
        [Ensures("Implies(!Result, @this.SpecItems == Old(@this.SpecItems) && @this.SpecCount == Old(@this.SpecCount))")]
        [Ensures("Implies(!Result, HashSet<T>.Mem(@this.SpecComparer, @this.SpecItems, value))")]
        [Ensures("HashSet<T>.SameEquality(Old(@this.SpecComparer), @this.SpecComparer)")]
        [Rlimit(2)]
        private bool AddIfNotPresent(T value, out int location)
        {
            Ghost<int> liveIn = _count - _freeCount;
            if (_buckets == null)
            {
                Initialize(0);
            }
            Debug.Assert(_buckets != null);

            Entry[]? entries = _entries;
            Debug.Assert(entries != null, "expected entries to be non-null");

            IEqualityComparer<T>? comparer = _comparer;
            int hashCode;

            uint collisionCount = 0;
            ref int bucket = ref Unsafe.NullRef<int>();

            if (typeof(T).IsValueType && // comparer can only be null for value types; enable JIT to eliminate entire if block for ref types
                comparer == null)
            {
                hashCode = value!.GetHashCode();
                SearchStart(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value);
                bucket = ref GetBucketRef(hashCode);
                int i = bucket - 1; // Value in _buckets is 1-based

                // ValueType: Devirtualize with EqualityComparer<TValue>.Default intrinsic
                while ((uint)i < (uint)entries.Length)
                {
                    Pal.Invariant(collisionCount <= (uint)entries.Length);
                    Pal.Invariant(Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, value, i, collisionCount));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), !Pal.Result<bool>() && Mem(_comparer, ItemsOf(Pal.Contents(entries), _count), value)));
                    Pal.Decreases((uint)entries.Length - collisionCount);
                    ref Entry entry = ref entries[i];
                    if (entry.HashCode == hashCode && EqualityComparer<T>.Default.Equals(entry.Value, value))
                    {
                        SearchHit(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value, i, collisionCount);
                        location = i;
                        return false;
                    }
                    SearchStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value, i, collisionCount);
                    i = entry.Next;

                    collisionCount++;
                    if (collisionCount > (uint)entries.Length)
                    {
                        // The chain of entries forms a loop, which means a concurrent update has happened.
                        ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                    }
                }
                SearchAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value, i, collisionCount);
            }
            else
            {
                Debug.Assert(comparer is not null);
                hashCode = value != null ? comparer.GetHashCode(value) : 0;
                SearchStart(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value);
                bucket = ref GetBucketRef(hashCode);
                int i = bucket - 1; // Value in _buckets is 1-based
                while ((uint)i < (uint)entries.Length)
                {
                    Pal.Invariant(collisionCount <= (uint)entries.Length);
                    Pal.Invariant(Search(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, _comparer, value, i, collisionCount));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), !Pal.Result<bool>() && Mem(_comparer, ItemsOf(Pal.Contents(entries), _count), value)));
                    Pal.Decreases((uint)entries.Length - collisionCount);
                    ref Entry entry = ref entries[i];
                    if (entry.HashCode == hashCode && comparer.Equals(entry.Value, value))
                    {
                        SearchHit(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value, i, collisionCount);
                        location = i;
                        return false;
                    }
                    SearchStep(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value, i, collisionCount);
                    i = entry.Next;

                    collisionCount++;
                    if (collisionCount > (uint)entries.Length)
                    {
                        // The chain of entries forms a loop, which means a concurrent update has happened.
                        ThrowHelper.ThrowInvalidOperationException_ConcurrentOperationsNotSupported();
                    }
                }
                SearchAbsent(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value, i, collisionCount);
            }

            Ghost<Seq<T>> items0 = ItemsOf(Pal.Contents(entries), _count);
            Ghost<int> count0 = _count;
            Ghost<int> live0 = _count - _freeCount;
            Pal.Assert(live0.Value == liveIn.Value);
            InsertPre(Pal.Contents(_buckets), Pal.Contents(entries), _count, _freeList, _freeCount, comparer, value);
            int index;
            if (_freeCount > 0)
            {
                index = _freeList;
                _freeCount--;
                Debug.Assert((StartOfFreeList - entries[_freeList].Next) >= -1, "shouldn't overflow because `next` cannot underflow");
                _freeList = StartOfFreeList - entries[_freeList].Next;
                Pal.Assert(_count == count0.Value && _freeCount >= 0 && HashSet<T>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), count0.Value, index, _freeCount + 1, comparer) && _freeList == HashSet<T>.FNext(Pal.Contents(entries), index));
                Pal.Assert(0 <= index && index < entries.Length);
            }
            else
            {
                int count = _count;
                if (count == entries.Length)
                {
                    Resize();
                    bucket = ref GetBucketRef(hashCode);
                    InsertPre(Pal.Contents(_buckets), Pal.Contents(_entries), _count, _freeList, _freeCount, comparer, value);
                }
                index = count;
                _count = count + 1;
                entries = _entries;
                Pal.Assert(_freeCount == 0 && index == count0.Value && _count == count0.Value + 1 && HashSet<T>.Wf(Pal.Contents(_buckets), Pal.Contents(entries), count0.Value, _freeList, 0, comparer));
                Pal.Assert(0 <= index && index < entries.Length);
            }

            Ghost<Seq<int>> buckets0 = Pal.Contents(_buckets);
            Ghost<Seq<Entry>> entries0 = Pal.Contents(entries);
            {
                ref Entry entry = ref entries![index];
                entry.HashCode = hashCode;
                entry.Next = bucket - 1; // Value in _buckets is 1-based
                entry.Value = value;
                bucket = index + 1;
                _version++;
                location = index;
            }
            InsertOk(buckets0.Value, Pal.Contents(_buckets), entries0.Value, Pal.Contents(entries), count0.Value, _count, _freeList, _freeCount, index, comparer, value);
            Pal.Assert(HashSet<T>.Added(items0.Value, ItemsOf(Pal.Contents(_entries), _count), value));
            Pal.Assert(_comparer == comparer && _count - _freeCount == live0.Value + 1);

            SameRefl(comparer);
            // Value types never rehash
            if (!typeof(T).IsValueType && collisionCount > HashHelpers.HashCollisionThreshold && comparer is NonRandomizedStringEqualityComparer)
            {
                // If we hit the collision threshold we'll need to switch to the comparer which is using randomized string hashing
                // i.e. EqualityComparer<string>.Default.
                AddedMem(comparer, items0.Value, ItemsOf(Pal.Contents(entries), _count), value);
                Resize(entries.Length, forceNewHashCodes: true);
                Pal.Assert(HashSet<T>.Added(items0.Value, ItemsOf(Pal.Contents(_entries), _count), value) && HashSet<T>.SameEquality(comparer, _comparer) && _count - _freeCount == live0.Value + 1);
                MemSame(comparer, _comparer, ItemsOf(Pal.Contents(_entries), _count), value);
                Pal.Assert(HashSet<T>.Mem(_comparer, ItemsOf(Pal.Contents(_entries), _count), value));
                location = FindItemIndex(value);
                Debug.Assert(location >= 0);
                Pal.Assert(location >= 0);
                Pal.Assert(HashSet<T>.Added(items0.Value, ItemsOf(Pal.Contents(_entries), _count), value) && HashSet<T>.SameEquality(comparer, _comparer) && _count - _freeCount == live0.Value + 1);
            }
            Pal.Assert(HashSet<T>.Added(items0.Value, ItemsOf(Pal.Contents(_entries), _count), value));
            Pal.Assert(HashSet<T>.SameEquality(comparer, _comparer) && _count - _freeCount == live0.Value + 1);

            return true;
        }

        /// <summary>
        /// Implementation Notes:
        /// If other is a hashset and is using same equality comparer, then checking subset is
        /// faster. Simply check that each element in this is in other.
        ///
        /// Note: if other doesn't use same equality comparer, then Contains check is invalid,
        /// which is why callers must take are of this.
        ///
        /// If callers are concerned about whether this is a proper subset, they take care of that.
        /// </summary>
        // R30.35. A walk over this set's prefixes (`MoveNext` states the walk); `HashSetChain.all_in_snoc` is a pattern.
        [Ensures("Pal.Implies(Result, HashSet<T>.AllIn(other.SpecComparer, other.SpecItems, @this.SpecItems))")]
        [Ensures("Pal.Implies(!Result, !HashSet<T>.AllIn(other.SpecComparer, other.SpecItems, @this.SpecItems))")]
        internal bool IsSubsetOfHashSetWithSameComparer(HashSet<T> other)
        {
            foreach (T item in this)
            {
                Pal.Invariant(Pal.Enumerator<Enumerator>(item).SpecFresh &&
                              0 <= Pal.Enumerator<Enumerator>(item).SpecIndex &&
                              Pal.Enumerator<Enumerator>(item).SpecIndex <= this.SpecSlots &&
                              (Pal.Returned()
                                  ? !Pal.ReturnValue<bool>() && !HashSet<T>.AllIn(other.SpecComparer, other.SpecItems, this.SpecItems)
                                  : Pal.Implies(Pal.Enumerator<Enumerator>(item).SpecIndex != 0,
                                        this.SpecPrefixes.Length == this.SpecSlots + 1 &&
                                        HashSet<T>.AllIn(other.SpecComparer, other.SpecItems,
                                            this.SpecPrefixes[Pal.Enumerator<Enumerator>(item).SpecIndex]))));
                Pal.Decreases(this.SpecSlots - Pal.Enumerator<Enumerator>(item).SpecIndex);
                if (!other.Contains(item))
                {
                    AllInWalk(other.SpecComparer, other.SpecItems, this.SpecPrefixes, this.SpecItems,
                        Pal.Enumerator<Enumerator>(item).SpecIndex);
                    return false;
                }
            }

            return true;
        }

        /// <summary>
        /// If other is a hashset that uses same equality comparer, intersect is much faster
        /// because we can use other's Contains
        /// </summary>
        private void IntersectWithHashSetWithSameComparer(HashSet<T> other)
        {
            Entry[]? entries = _entries;
            for (int i = 0; i < _count; i++)
            {
                ref Entry entry = ref entries![i];
                if (entry.Next >= -1)
                {
                    T item = entry.Value;
                    if (!other.Contains(item))
                    {
                        Remove(item);
                    }
                }
            }
        }

        /// <summary>
        /// Iterate over other. If contained in this, mark an element in bit array corresponding to
        /// its position in _slots. If anything is unmarked (in bit array), remove it.
        ///
        /// This attempts to allocate on the stack, if below StackAllocThreshold.
        /// </summary>
        private unsafe void IntersectWithEnumerable(IEnumerable<T> other)
        {
            Debug.Assert(_buckets != null, "_buckets shouldn't be null; callers should check first");

            // Keep track of current last index; don't want to move past the end of our bit array
            // (could happen if another thread is modifying the collection).
            int originalCount = _count;
            int intArrayLength = BitHelper.ToIntArrayLength(originalCount);

            Span<int> span = stackalloc int[StackAllocThreshold];
            BitHelper bitHelper = (uint)intArrayLength <= StackAllocThreshold ?
                new BitHelper(span.Slice(0, intArrayLength), clear: true) :
                new BitHelper(new int[intArrayLength], clear: false);

            // Mark if contains: find index of in slots array and mark corresponding element in bit array.
            foreach (T item in other)
            {
                int index = FindItemIndex(item);
                if (index >= 0)
                {
                    bitHelper.MarkBit(index);
                }
            }

            // If anything unmarked, remove it. Perf can be optimized here if BitHelper had a
            // FindFirstUnmarked method.
            for (int i = 0; i < originalCount; i++)
            {
                ref Entry entry = ref _entries![i];
                if (entry.Next >= -1 && !bitHelper.IsMarked(i))
                {
                    Remove(entry.Value);
                }
            }
        }

        /// <summary>
        /// if other is a set, we can assume it doesn't have duplicate elements, so use this
        /// technique: if can't remove, then it wasn't present in this set, so add.
        ///
        /// As with other methods, callers take care of ensuring that other is a hashset using the
        /// same equality comparer.
        /// </summary>
        /// <param name="other"></param>
        private void SymmetricExceptWithUniqueHashSet(HashSet<T> other)
        {
            foreach (T item in other)
            {
                if (!Remove(item))
                {
                    AddIfNotPresent(item, out _);
                }
            }
        }

        /// <summary>
        /// Implementation notes:
        ///
        /// Used for symmetric except when other isn't a HashSet. This is more tedious because
        /// other may contain duplicates. HashSet technique could fail in these situations:
        /// 1. Other has a duplicate that's not in this: HashSet technique would add then
        /// remove it.
        /// 2. Other has a duplicate that's in this: HashSet technique would remove then add it
        /// back.
        /// In general, its presence would be toggled each time it appears in other.
        ///
        /// This technique uses bit marking to indicate whether to add/remove the item. If already
        /// present in collection, it will get marked for deletion. If added from other, it will
        /// get marked as something not to remove.
        ///
        /// </summary>
        /// <param name="other"></param>
        private unsafe void SymmetricExceptWithEnumerable(IEnumerable<T> other)
        {
            int originalCount = _count;
            int intArrayLength = BitHelper.ToIntArrayLength(originalCount);

            Span<int> itemsToRemoveSpan = stackalloc int[StackAllocThreshold / 2];
            BitHelper itemsToRemove = intArrayLength <= StackAllocThreshold / 2 ?
                new BitHelper(itemsToRemoveSpan.Slice(0, intArrayLength), clear: true) :
                new BitHelper(new int[intArrayLength], clear: false);

            Span<int> itemsAddedFromOtherSpan = stackalloc int[StackAllocThreshold / 2];
            BitHelper itemsAddedFromOther = intArrayLength <= StackAllocThreshold / 2 ?
                new BitHelper(itemsAddedFromOtherSpan.Slice(0, intArrayLength), clear: true) :
                new BitHelper(new int[intArrayLength], clear: false);

            foreach (T item in other)
            {
                int location;
                if (AddIfNotPresent(item, out location))
                {
                    // wasn't already present in collection; flag it as something not to remove
                    // *NOTE* if location is out of range, we should ignore. BitHelper will
                    // detect that it's out of bounds and not try to mark it. But it's
                    // expected that location could be out of bounds because adding the item
                    // will increase _lastIndex as soon as all the free spots are filled.
                    itemsAddedFromOther.MarkBit(location);
                }
                else
                {
                    // already there...if not added from other, mark for remove.
                    // *NOTE* Even though BitHelper will check that location is in range, we want
                    // to check here. There's no point in checking items beyond originalCount
                    // because they could not have been in the original collection
                    if (location < originalCount && !itemsAddedFromOther.IsMarked(location))
                    {
                        itemsToRemove.MarkBit(location);
                    }
                }
            }

            // if anything marked, remove it
            for (int i = 0; i < originalCount; i++)
            {
                if (itemsToRemove.IsMarked(i))
                {
                    Remove(_entries![i].Value);
                }
            }
        }

        /// <summary>
        /// Determines counts that can be used to determine equality, subset, and superset. This
        /// is only used when other is an IEnumerable and not a HashSet. If other is a HashSet
        /// these properties can be checked faster without use of marking because we can assume
        /// other has no duplicates.
        ///
        /// The following count checks are performed by callers:
        /// 1. Equals: checks if unfoundCount = 0 and uniqueFoundCount = _count; i.e. everything
        /// in other is in this and everything in this is in other
        /// 2. Subset: checks if unfoundCount >= 0 and uniqueFoundCount = _count; i.e. other may
        /// have elements not in this and everything in this is in other
        /// 3. Proper subset: checks if unfoundCount > 0 and uniqueFoundCount = _count; i.e
        /// other must have at least one element not in this and everything in this is in other
        /// 4. Proper superset: checks if unfound count = 0 and uniqueFoundCount strictly less
        /// than _count; i.e. everything in other was in this and this had at least one element
        /// not contained in other.
        ///
        /// An earlier implementation used delegates to perform these checks rather than returning
        /// an ElementCount struct; however this was changed due to the perf overhead of delegates.
        /// </summary>
        /// <param name="other"></param>
        /// <param name="returnIfUnfound">Allows us to finish faster for equals and proper superset
        /// because unfoundCount must be 0.</param>
        private unsafe (int UniqueCount, int UnfoundCount) CheckUniqueAndUnfoundElements(IEnumerable<T> other, bool returnIfUnfound)
        {
            // Need special case in case this has no elements.
            if (_count == 0)
            {
                int numElementsInOther = 0;
                foreach (T item in other)
                {
                    numElementsInOther++;
                    break; // break right away, all we want to know is whether other has 0 or 1 elements
                }

                return (UniqueCount: 0, UnfoundCount: numElementsInOther);
            }

            Debug.Assert((_buckets != null) && (_count > 0), "_buckets was null but count greater than 0");

            int originalCount = _count;
            int intArrayLength = BitHelper.ToIntArrayLength(originalCount);

            Span<int> span = stackalloc int[StackAllocThreshold];
            BitHelper bitHelper = intArrayLength <= StackAllocThreshold ?
                new BitHelper(span.Slice(0, intArrayLength), clear: true) :
                new BitHelper(new int[intArrayLength], clear: false);

            int unfoundCount = 0; // count of items in other not found in this
            int uniqueFoundCount = 0; // count of unique items in other found in this

            foreach (T item in other)
            {
                int index = FindItemIndex(item);
                if (index >= 0)
                {
                    if (!bitHelper.IsMarked(index))
                    {
                        // Item hasn't been seen yet.
                        bitHelper.MarkBit(index);
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

            return (uniqueFoundCount, unfoundCount);
        }

        /// <summary>
        /// Checks if equality comparers are equal. This is used for algorithms that can
        /// speed up if it knows the other item has unique elements. I.e. if they're using
        /// different equality comparers, then uniqueness assumption between sets break.
        /// </summary>
        internal static bool EqualityComparersAreEqual(HashSet<T> set1, HashSet<T> set2) => set1.Comparer.Equals(set2.Comparer);

        /// <summary>
        /// Checks if effective equality comparers are equal. This is used for algorithms that
        /// require that both collections use identical hashing implementations for their entries.
        /// </summary>
        internal static bool EffectiveEqualityComparersAreEqual(HashSet<T> set1, HashSet<T> set2) => set1.EffectiveComparer.Equals(set2.EffectiveComparer);

        #endregion

        private struct Entry
        {
            public int HashCode;
            /// <summary>
            /// 0-based index of next entry in chain: -1 means end of chain
            /// also encodes whether this entry _itself_ is part of the free list by changing sign and subtracting 3,
            /// so -2 means end of free list, -3 means index 0 but on free list, -4 means index 1 but on free list, etc.
            /// </summary>
            public int Next;
            public T Value;
        }

        public struct Enumerator : IEnumerator<T>
        {
            private readonly HashSet<T> _hashSet;
            private readonly int _version;
            private int _index;
            private T _current;

            [Spec] internal SpecInt SpecIndex => _index;
            [Spec] internal bool SpecFresh => _version == _hashSet.SpecVersion;

            [Ensures("ReferenceEquals(@this._hashSet, hashSet) && @this._version == hashSet.SpecVersion && @this._index == 0")]
            [Ensures("hashSet.SpecSlots >= 0")]
            internal Enumerator(HashSet<T> hashSet)
            {
                _hashSet = hashSet;
                _version = hashSet._version;
                _index = 0;
                _current = default!;
            }

            [Requires("0 <= @this._index && @this._index <= @this._hashSet.SpecSlots + 1")]
            [Throws(typeof(InvalidOperationException), "@this._version != @this._hashSet.SpecVersion")]
            [Ensures("@this._version == @this._hashSet.SpecVersion")]
            [Ensures("0 <= @this._index && @this._index <= @this._hashSet.SpecSlots + 1")]
            [Ensures("@this._hashSet.SpecPrefixes.Length == @this._hashSet.SpecSlots + 1")]
            [Ensures("Pal.Implies(Result, Pal.Old(@this._index) < @this._index && @this._index <= @this._hashSet.SpecSlots && " +
                "@this._hashSet.SpecPrefixes[@this._index] == Pal.Snoc(@this._hashSet.SpecPrefixes[Pal.Old(@this._index)], @this._current))")]
            [Ensures("Pal.Implies(!Result, @this._index == @this._hashSet.SpecSlots + 1)")]
            [Ensures("Pal.Implies(!Result && Pal.Old(@this._index) <= @this._hashSet.SpecSlots, " +
                "@this._hashSet.SpecPrefixes[@this._hashSet.SpecSlots] == @this._hashSet.SpecPrefixes[Pal.Old(@this._index)])")]
            [Ensures("HashSet<T>.Walk(@this._hashSet.SpecPrefixes, @this._hashSet.SpecItems) && @this._hashSet.SpecPrefixes[0].Length == 0")]
            public bool MoveNext()
            {
                if (_version != _hashSet._version)
                {
                    ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                }

                PrefixesWalk(Pal.Contents(_hashSet._entries), _hashSet._count);

                Ghost<int> index0 = _index;
                Ghost<Seq<T>> before = ItemsOf(Pal.Contents(_hashSet._entries), Math.Min(_index, _hashSet._count));
                // Use unsigned comparison since we set index to dictionary.count+1 when the enumeration ends.
                // dictionary.count+1 could be negative if dictionary.count is int.MaxValue
                while ((uint)_index < (uint)_hashSet._count)
                {
                    Pal.Invariant(index0.Value <= _index && _index <= _hashSet._count + 1);
                    Pal.Invariant(Pal.Implies(index0.Value <= _hashSet._count, _index <= _hashSet._count));
                    Pal.Invariant(Pal.Implies(!Pal.Returned() && index0.Value <= _hashSet._count,
                        ItemsOf(Pal.Contents(_hashSet._entries), _index) == before.Value));
                    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>() && index0.Value < _index &&
                        ItemsOf(Pal.Contents(_hashSet._entries), _index) == Pal.Snoc(before.Value, _current)));
                    Pal.Decreases(_hashSet._count - _index);
                    ref Entry entry = ref _hashSet._entries![_index++];
                    ItemsStep(Pal.Contents(_hashSet._entries), _index - 1);
                    if (entry.Next >= -1)
                    {
                        _current = entry.Value;
                        return true;
                    }
                }

                _index = _hashSet._count + 1;
                _current = default!;
                return false;
            }

            [Ensures("Pal.Same(Result, @this._current)")]
            public T Current => _current;

            [Ensures("true")]
            public void Dispose() { }

            [Throws(typeof(InvalidOperationException), "@this._index == 0 || @this._index == @this._hashSet.SpecSlots + 1")]
            [Ensures("Pal.Boxes(Result, @this._current)")]
            object? IEnumerator.Current
            {
                get
                {
                    if (_index == 0 || (_index == _hashSet._count + 1))
                    {
                        ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen();
                    }

                    return _current;
                }
            }

            [Throws(typeof(InvalidOperationException), "@this._version != @this._hashSet.SpecVersion")]
            [Ensures("@this._version == @this._hashSet.SpecVersion && @this._index == 0")]
            void IEnumerator.Reset()
            {
                if (_version != _hashSet._version)
                {
                    ThrowHelper.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion();
                }

                _index = 0;
                _current = default!;
            }
        }
    }
}
