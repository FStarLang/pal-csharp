// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.Serialization;
using PalLang;

namespace System.Collections.Generic
{
    /// <summary>
    /// The abstraction of a <see cref="SortedDictionary{TKey, TValue}"/> (doc/translation.md
    /// R27.58): its pairs, in key order, and the comparer of their keys.
    /// </summary>
    [Spec]
    public struct SortedDictionaryModel<TKey, TValue>
    {
        public Seq<KeyValuePair<TKey, TValue>> Pairs;
        public IComparer<KeyValuePair<TKey, TValue>> PairComparer;
        public IComparer<TKey> KeyComparer;
    }

    [DebuggerTypeProxy(typeof(IDictionaryDebugView<,>))]
    [DebuggerDisplay("Count = {Count}")]
    [Serializable]
    [System.Runtime.CompilerServices.TypeForwardedFrom("System, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    public class SortedDictionary<TKey, TValue> : IDictionary<TKey, TValue>, IDictionary, IReadOnlyDictionary<TKey, TValue> where TKey : notnull
    {
        [NonSerialized]
        private KeyCollection? _keys;
        [NonSerialized]
        private ValueCollection? _values;

        private readonly TreeSet<KeyValuePair<TKey, TValue>> _set; // Do not rename (binary serialization)

        [Refine("Result.PairComparer == SpecKeyMap.OfKeys<TKey, TValue>(Result.KeyComparer)")]
        [Model]
        private SortedDictionaryModel<TKey, TValue> Model => new SortedDictionaryModel<TKey, TValue>
        {
            Pairs = _set.SpecItems,
            PairComparer = _set.SpecComparer,
            KeyComparer = SpecKeyMap.KeyOf(_set.SpecComparer),
        };

        /// <summary>The pairs, in key order.</summary>
        [Spec]
        public Seq<KeyValuePair<TKey, TValue>> SpecPairs => Model.Pairs;

        /// <summary>The keys, in order: strictly sorted under <see cref="SpecKeyComparer"/>.</summary>
        [Spec]
        public Seq<TKey> SpecKeys => SpecKeyMap.Keys(Model.Pairs);

        [Spec]
        public IComparer<TKey> SpecKeyComparer => Model.KeyComparer;

        /// <summary>The comparer of the pair set: <see cref="SpecKeyComparer"/> on the keys.</summary>
        [Spec]
        public IComparer<KeyValuePair<TKey, TValue>> SpecPairComparer => Model.PairComparer;

        [Ensures("@this.SpecPairs.Length == 0")]
        [Ensures("@this.SpecKeyComparer == Comparer<TKey>.Default")]
        public SortedDictionary() : this((IComparer<TKey>?)null)
        {
        }

        public SortedDictionary(IDictionary<TKey, TValue> dictionary) : this(dictionary, null)
        {
        }

        public SortedDictionary(IDictionary<TKey, TValue> dictionary, IComparer<TKey>? comparer)
        {
            ArgumentNullException.ThrowIfNull(dictionary);

            var keyValuePairComparer = new KeyValuePairComparer(comparer);

            if (dictionary is SortedDictionary<TKey, TValue> sortedDictionary &&
                sortedDictionary._set.Comparer is KeyValuePairComparer kv &&
                kv.keyComparer.Equals(keyValuePairComparer.keyComparer))
            {
                _set = new TreeSet<KeyValuePair<TKey, TValue>>(sortedDictionary._set, keyValuePairComparer);
            }
            else
            {
                _set = new TreeSet<KeyValuePair<TKey, TValue>>(keyValuePairComparer);

                foreach (KeyValuePair<TKey, TValue> pair in dictionary)
                {
                    _set.Add(pair);
                }
            }
        }

        [Ensures("@this.SpecPairs.Length == 0")]
        [Ensures("@this.SpecKeyComparer == (comparer == null ? Comparer<TKey>.Default : comparer)")]
        public SortedDictionary(IComparer<TKey>? comparer)
        {
            _set = new TreeSet<KeyValuePair<TKey, TValue>>(new KeyValuePairComparer(comparer));
        }

        void ICollection<KeyValuePair<TKey, TValue>>.Add(KeyValuePair<TKey, TValue> keyValuePair)
        {
            _set.Add(keyValuePair);
        }

        bool ICollection<KeyValuePair<TKey, TValue>>.Contains(KeyValuePair<TKey, TValue> keyValuePair)
        {
            TreeSet<KeyValuePair<TKey, TValue>>.Node? node = _set.FindNode(keyValuePair);
            if (node == null)
            {
                return false;
            }

            if (keyValuePair.Value == null)
            {
                return node.Item.Value == null;
            }
            else
            {
                return EqualityComparer<TValue>.Default.Equals(node.Item.Value, keyValuePair.Value);
            }
        }

        bool ICollection<KeyValuePair<TKey, TValue>>.Remove(KeyValuePair<TKey, TValue> keyValuePair)
        {
            TreeSet<KeyValuePair<TKey, TValue>>.Node? node = _set.FindNode(keyValuePair);
            if (node == null)
            {
                return false;
            }

            if (EqualityComparer<TValue>.Default.Equals(node.Item.Value, keyValuePair.Value))
            {
                _set.Remove(keyValuePair);
                return true;
            }
            return false;
        }

        bool ICollection<KeyValuePair<TKey, TValue>>.IsReadOnly
        {
            get
            {
                return false;
            }
        }

        public TValue this[TKey key]
        {
            [Ensures("Pal.KeyIndex(@this.SpecKeyComparer, @this.SpecKeys, key) >= 0")]
            [Ensures("Pal.Same(Result, @this.SpecPairs[Pal.KeyIndex(@this.SpecKeyComparer, @this.SpecKeys, key)].Value)")]
            [Ensures("@this.SpecPairs == Pal.Old(@this.SpecPairs)")]
            [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
            [Throws(typeof(KeyNotFoundException), "Pal.KeyIndex(@this.SpecKeyComparer, @this.SpecKeys, key) < 0")]
            get
            {
                ArgumentNullException.ThrowIfNull(key);

                TreeSet<KeyValuePair<TKey, TValue>>.Node? node = _set.FindNode(new KeyValuePair<TKey, TValue>(key, default(TValue)!));
                if (node == null)
                {
                    throw new KeyNotFoundException(SR.Format(SR.Arg_KeyNotFoundWithKey, key.ToString()));
                }

                return node.Item.Value;
            }
            set
            {
                ArgumentNullException.ThrowIfNull(key);

                TreeSet<KeyValuePair<TKey, TValue>>.Node? node = _set.FindNode(new KeyValuePair<TKey, TValue>(key, default(TValue)!));
                if (node == null)
                {
                    _set.Add(new KeyValuePair<TKey, TValue>(key, value));
                }
                else
                {
                    node.Item = new KeyValuePair<TKey, TValue>(node.Item.Key, value);
                    _set.UpdateVersion();
                }
            }
        }

        [Ensures("Result == @this.SpecPairs.Length")]
        public int Count
        {
            get
            {
                return _set.Count;
            }
        }

        public IComparer<TKey> Comparer
        {
            get
            {
                return ((KeyValuePairComparer)_set.Comparer).keyComparer;
            }
        }

        public KeyCollection Keys => _keys ??= new KeyCollection(this);

        ICollection<TKey> IDictionary<TKey, TValue>.Keys
        {
            get
            {
                return Keys;
            }
        }

        IEnumerable<TKey> IReadOnlyDictionary<TKey, TValue>.Keys
        {
            get
            {
                return Keys;
            }
        }

        public ValueCollection Values => _values ??= new ValueCollection(this);

        ICollection<TValue> IDictionary<TKey, TValue>.Values
        {
            get
            {
                return Values;
            }
        }

        IEnumerable<TValue> IReadOnlyDictionary<TKey, TValue>.Values
        {
            get
            {
                return Values;
            }
        }

        [Requires("@this.SpecPairs.Length < int.MaxValue")]
        [Ensures("@this.SpecPairs == SpecTopDown.Inserted(Pal.Old(@this.SpecPairComparer), Pal.Old(@this.SpecPairs), new KeyValuePair<TKey, TValue>(key, value))")]
        [Ensures("@this.SpecKeyComparer == Pal.Old(@this.SpecKeyComparer)")]
        [Requires("!Pal.IsNull(key)")]
        [Requires("Pal.KeyIndex(@this.SpecKeyComparer, @this.SpecKeys, key) < 0")]
        public void Add(TKey key, TValue value)
        {
            ArgumentNullException.ThrowIfNull(key);

            _set.Add(new KeyValuePair<TKey, TValue>(key, value));
        }

        [Ensures("@this.SpecPairs.Length == 0")]
        [Ensures("@this.SpecKeyComparer == Pal.Old(@this.SpecKeyComparer)")]
        public void Clear()
        {
            _set.Clear();
        }

        [Ensures("Result == (Pal.KeyIndex(@this.SpecKeyComparer, @this.SpecKeys, key) >= 0)")]
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        public bool ContainsKey(TKey key)
        {
            ArgumentNullException.ThrowIfNull(key);

            return _set.Contains(new KeyValuePair<TKey, TValue>(key, default(TValue)!));
        }

        public bool ContainsValue(TValue value)
        {
            bool found = false;
            if (value == null)
            {
                _set.InOrderTreeWalk(delegate (TreeSet<KeyValuePair<TKey, TValue>>.Node node)
                {
                    if (node.Item.Value == null)
                    {
                        found = true;
                        return false;  // stop the walk
                    }
                    return true;
                });
            }
            else
            {
                EqualityComparer<TValue> valueComparer = EqualityComparer<TValue>.Default;
                _set.InOrderTreeWalk(delegate (TreeSet<KeyValuePair<TKey, TValue>>.Node node)
                {
                    if (valueComparer.Equals(node.Item.Value, value))
                    {
                        found = true;
                        return false;  // stop the walk
                    }
                    return true;
                });
            }
            return found;
        }

        [Requires("index >= 0")]
        [Requires("Pal.Contents(array).Length - index >= @this.SpecPairs.Length")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.SpecPairs.Length, @this.SpecPairs)")]
        [Ensures("@this.SpecPairs == Pal.Old(@this.SpecPairs)")]
        [Ensures("@this.SpecKeyComparer == Pal.Old(@this.SpecKeyComparer)")]
        public void CopyTo(KeyValuePair<TKey, TValue>[] array, int index)
        {
            _set.CopyTo(array, index);
        }

        public Enumerator GetEnumerator() => new Enumerator(this, Enumerator.KeyValuePair);

        IEnumerator<KeyValuePair<TKey, TValue>> IEnumerable<KeyValuePair<TKey, TValue>>.GetEnumerator() =>
            Count == 0 ? EnumerableHelpers.GetEmptyEnumerator<KeyValuePair<TKey, TValue>>() :
            _set.GetEnumerator();

        [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecKeyComparer), Pal.Old(@this.SpecKeys), key) >= 0)")]
        [Ensures("@this.SpecPairs == SpecTopDownRemove.Removed(Pal.Old(@this.SpecPairComparer), Pal.Old(@this.SpecPairs), new KeyValuePair<TKey, TValue>(key, default(TValue)!))")]
        [Ensures("@this.SpecKeyComparer == Pal.Old(@this.SpecKeyComparer)")]
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        public bool Remove(TKey key)
        {
            ArgumentNullException.ThrowIfNull(key);

            return _set.Remove(new KeyValuePair<TKey, TValue>(key, default(TValue)!));
        }

        [Ensures("Result == (Pal.KeyIndex(@this.SpecKeyComparer, @this.SpecKeys, key) >= 0)")]
        [Ensures("Pal.Implies(Result, Pal.Same(value, @this.SpecPairs[Pal.KeyIndex(@this.SpecKeyComparer, @this.SpecKeys, key)].Value))")]
        [Ensures("@this.SpecPairs == Pal.Old(@this.SpecPairs)")]
        [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
        public bool TryGetValue(TKey key, [MaybeNullWhen(false)] out TValue value)
        {
            ArgumentNullException.ThrowIfNull(key);

            TreeSet<KeyValuePair<TKey, TValue>>.Node? node = _set.FindNode(new KeyValuePair<TKey, TValue>(key, default(TValue)!));
            if (node == null)
            {
                value = default;
                return false;
            }
            value = node.Item.Value;
            return true;
        }

        void ICollection.CopyTo(Array array, int index)
        {
            ((ICollection)_set).CopyTo(array, index);
        }

        bool IDictionary.IsFixedSize
        {
            get { return false; }
        }

        bool IDictionary.IsReadOnly
        {
            get { return false; }
        }

        ICollection IDictionary.Keys
        {
            get { return Keys; }
        }

        ICollection IDictionary.Values
        {
            get { return Values; }
        }

        object? IDictionary.this[object key]
        {
            get
            {
                if (IsCompatibleKey(key))
                {
                    TValue? value;
                    if (TryGetValue((TKey)key, out value))
                    {
                        return value;
                    }
                }

                return null;
            }
            set
            {
                ArgumentNullException.ThrowIfNull(key);
                if (default(TValue) != null)
                {
                    ArgumentNullException.ThrowIfNull(value);
                }

                try
                {
                    TKey tempKey = (TKey)key;
                    try
                    {
                        this[tempKey] = (TValue)value!;
                    }
                    catch (InvalidCastException)
                    {
                        throw new ArgumentException(SR.Format(SR.Arg_WrongType, value, typeof(TValue)), nameof(value));
                    }
                }
                catch (InvalidCastException)
                {
                    throw new ArgumentException(SR.Format(SR.Arg_WrongType, key, typeof(TKey)), nameof(key));
                }
            }
        }

        void IDictionary.Add(object key, object? value)
        {
            ArgumentNullException.ThrowIfNull(key);

            if (default(TValue) != null)
            {
                ArgumentNullException.ThrowIfNull(value);
            }

            try
            {
                TKey tempKey = (TKey)key;

                try
                {
                    Add(tempKey, (TValue)value!);
                }
                catch (InvalidCastException)
                {
                    throw new ArgumentException(SR.Format(SR.Arg_WrongType, value, typeof(TValue)), nameof(value));
                }
            }
            catch (InvalidCastException)
            {
                throw new ArgumentException(SR.Format(SR.Arg_WrongType, key, typeof(TKey)), nameof(key));
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

        private static bool IsCompatibleKey(object key)
        {
            ArgumentNullException.ThrowIfNull(key);

            return (key is TKey);
        }

        IDictionaryEnumerator IDictionary.GetEnumerator() => new Enumerator(this, Enumerator.DictEntry);

        void IDictionary.Remove(object key)
        {
            if (IsCompatibleKey(key))
            {
                Remove((TKey)key);
            }
        }

        bool ICollection.IsSynchronized
        {
            get { return false; }
        }

        object ICollection.SyncRoot
        {
            get { return ((ICollection)_set).SyncRoot; }
        }

        IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<KeyValuePair<TKey, TValue>>)this).GetEnumerator();

        public struct Enumerator : IEnumerator<KeyValuePair<TKey, TValue>>, IDictionaryEnumerator
        {
            private TreeSet<KeyValuePair<TKey, TValue>>.Enumerator _treeEnum;
            private readonly int _getEnumeratorRetType;  // What should Enumerator.Current return?

            internal const int KeyValuePair = 1;
            internal const int DictEntry = 2;

            internal Enumerator(SortedDictionary<TKey, TValue> dictionary, int getEnumeratorRetType)
            {
                _treeEnum = dictionary._set.GetEnumerator();
                _getEnumeratorRetType = getEnumeratorRetType;
            }

            public bool MoveNext()
            {
                return _treeEnum.MoveNext();
            }

            public void Dispose()
            {
                _treeEnum.Dispose();
            }

            public KeyValuePair<TKey, TValue> Current
            {
                get
                {
                    return _treeEnum.Current;
                }
            }

            internal bool NotStartedOrEnded
            {
                get
                {
                    return _treeEnum.NotStartedOrEnded;
                }
            }

            internal void Reset()
            {
                _treeEnum.Reset();
            }


            void IEnumerator.Reset()
            {
                _treeEnum.Reset();
            }

            object? IEnumerator.Current
            {
                get
                {
                    if (NotStartedOrEnded)
                    {
                        throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                    }

                    if (_getEnumeratorRetType == DictEntry)
                    {
                        return new DictionaryEntry(Current.Key, Current.Value);
                    }

                    return Current;
                }
            }

            object IDictionaryEnumerator.Key
            {
                get
                {
                    if (NotStartedOrEnded)
                    {
                        throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                    }

                    return Current.Key;
                }
            }

            object? IDictionaryEnumerator.Value
            {
                get
                {
                    if (NotStartedOrEnded)
                    {
                        throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                    }

                    return Current.Value;
                }
            }

            DictionaryEntry IDictionaryEnumerator.Entry
            {
                get
                {
                    if (NotStartedOrEnded)
                    {
                        throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                    }

                    return new DictionaryEntry(Current.Key, Current.Value);
                }
            }
        }

        [DebuggerTypeProxy(typeof(DictionaryKeyCollectionDebugView<,>))]
        [DebuggerDisplay("Count = {Count}")]
        public sealed class KeyCollection : ICollection<TKey>, ICollection, IReadOnlyCollection<TKey>
        {
            private readonly SortedDictionary<TKey, TValue> _dictionary;

            public KeyCollection(SortedDictionary<TKey, TValue> dictionary)
            {
                ArgumentNullException.ThrowIfNull(dictionary);

                _dictionary = dictionary;
            }

            public Enumerator GetEnumerator() => new Enumerator(_dictionary);

            IEnumerator<TKey> IEnumerable<TKey>.GetEnumerator() =>
                Count == 0 ? EnumerableHelpers.GetEmptyEnumerator<TKey>() :
                GetEnumerator();

            IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<TKey>)this).GetEnumerator();

            public void CopyTo(TKey[] array, int index)
            {
                ArgumentNullException.ThrowIfNull(array);

                ArgumentOutOfRangeException.ThrowIfNegative(index);

                if (array.Length - index < Count)
                {
                    throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall);
                }

                _dictionary._set.InOrderTreeWalk(delegate (TreeSet<KeyValuePair<TKey, TValue>>.Node node) { array[index++] = node.Item.Key; return true; });
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
                        object[] objects = (object[])array;
                        _dictionary._set.InOrderTreeWalk(delegate (TreeSet<KeyValuePair<TKey, TValue>>.Node node) { objects[index++] = node.Item.Key; return true; });
                    }
                    catch (ArrayTypeMismatchException)
                    {
                        throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                    }
                }
            }

            public int Count
            {
                get { return _dictionary.Count; }
            }

            bool ICollection<TKey>.IsReadOnly
            {
                get { return true; }
            }

            void ICollection<TKey>.Add(TKey item)
            {
                throw new NotSupportedException(SR.NotSupported_KeyCollectionSet);
            }

            void ICollection<TKey>.Clear()
            {
                throw new NotSupportedException(SR.NotSupported_KeyCollectionSet);
            }

            public bool Contains(TKey item)
            {
                return _dictionary.ContainsKey(item);
            }

            bool ICollection<TKey>.Remove(TKey item)
            {
                throw new NotSupportedException(SR.NotSupported_KeyCollectionSet);
            }

            bool ICollection.IsSynchronized
            {
                get { return false; }
            }

            object ICollection.SyncRoot
            {
                get { return ((ICollection)_dictionary).SyncRoot; }
            }

            public struct Enumerator : IEnumerator<TKey>, IEnumerator
            {
                private SortedDictionary<TKey, TValue>.Enumerator _dictEnum;

                internal Enumerator(SortedDictionary<TKey, TValue> dictionary)
                {
                    _dictEnum = dictionary.GetEnumerator();
                }

                public void Dispose()
                {
                    _dictEnum.Dispose();
                }

                public bool MoveNext()
                {
                    return _dictEnum.MoveNext();
                }

                public TKey Current
                {
                    get
                    {
                        return _dictEnum.Current.Key;
                    }
                }

                object? IEnumerator.Current
                {
                    get
                    {
                        if (_dictEnum.NotStartedOrEnded)
                        {
                            throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                        }

                        return Current;
                    }
                }

                void IEnumerator.Reset()
                {
                    _dictEnum.Reset();
                }
            }
        }

        [DebuggerTypeProxy(typeof(DictionaryValueCollectionDebugView<,>))]
        [DebuggerDisplay("Count = {Count}")]
        public sealed class ValueCollection : ICollection<TValue>, ICollection, IReadOnlyCollection<TValue>
        {
            private readonly SortedDictionary<TKey, TValue> _dictionary;

            public ValueCollection(SortedDictionary<TKey, TValue> dictionary)
            {
                ArgumentNullException.ThrowIfNull(dictionary);

                _dictionary = dictionary;
            }

            public Enumerator GetEnumerator() => new Enumerator(_dictionary);

            IEnumerator<TValue> IEnumerable<TValue>.GetEnumerator() =>
                Count == 0 ? EnumerableHelpers.GetEmptyEnumerator<TValue>() :
                GetEnumerator();

            IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable<TValue>)this).GetEnumerator();

            public void CopyTo(TValue[] array, int index)
            {
                ArgumentNullException.ThrowIfNull(array);

                ArgumentOutOfRangeException.ThrowIfNegative(index);

                if (array.Length - index < Count)
                {
                    throw new ArgumentException(SR.Arg_ArrayPlusOffTooSmall);
                }

                _dictionary._set.InOrderTreeWalk(delegate (TreeSet<KeyValuePair<TKey, TValue>>.Node node) { array[index++] = node.Item.Value; return true; });
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
                        object?[] objects = (object?[])array;
                        _dictionary._set.InOrderTreeWalk(delegate (TreeSet<KeyValuePair<TKey, TValue>>.Node node) { objects[index++] = node.Item.Value; return true; });
                    }
                    catch (ArrayTypeMismatchException)
                    {
                        throw new ArgumentException(SR.Argument_IncompatibleArrayType, nameof(array));
                    }
                }
            }

            public int Count
            {
                get { return _dictionary.Count; }
            }

            bool ICollection<TValue>.IsReadOnly
            {
                get { return true; }
            }

            void ICollection<TValue>.Add(TValue item)
            {
                throw new NotSupportedException(SR.NotSupported_ValueCollectionSet);
            }

            void ICollection<TValue>.Clear()
            {
                throw new NotSupportedException(SR.NotSupported_ValueCollectionSet);
            }

            bool ICollection<TValue>.Contains(TValue item)
            {
                return _dictionary.ContainsValue(item);
            }

            bool ICollection<TValue>.Remove(TValue item)
            {
                throw new NotSupportedException(SR.NotSupported_ValueCollectionSet);
            }

            bool ICollection.IsSynchronized
            {
                get { return false; }
            }

            object ICollection.SyncRoot
            {
                get { return ((ICollection)_dictionary).SyncRoot; }
            }

            public struct Enumerator : IEnumerator<TValue>, IEnumerator
            {
                private SortedDictionary<TKey, TValue>.Enumerator _dictEnum;

                internal Enumerator(SortedDictionary<TKey, TValue> dictionary)
                {
                    _dictEnum = dictionary.GetEnumerator();
                }

                public void Dispose()
                {
                    _dictEnum.Dispose();
                }

                public bool MoveNext()
                {
                    return _dictEnum.MoveNext();
                }

                public TValue Current
                {
                    get
                    {
                        return _dictEnum.Current.Value;
                    }
                }

                object? IEnumerator.Current
                {
                    get
                    {
                        if (_dictEnum.NotStartedOrEnded)
                        {
                            throw new InvalidOperationException(SR.InvalidOperation_EnumOpCantHappen);
                        }

                        return Current;
                    }
                }

                void IEnumerator.Reset()
                {
                    _dictEnum.Reset();
                }
            }
        }

        [Serializable]
        public sealed class KeyValuePairComparer : Comparer<KeyValuePair<TKey, TValue>>
        {
            internal IComparer<TKey> keyComparer; // Do not rename (binary serialization)

            public KeyValuePairComparer(IComparer<TKey>? keyComparer)
            {
                this.keyComparer = keyComparer ?? Comparer<TKey>.Default;
            }

            public override int Compare(KeyValuePair<TKey, TValue> x, KeyValuePair<TKey, TValue> y)
            {
                return keyComparer.Compare(x.Key, y.Key);
            }

            public override bool Equals(object? obj)
            {
                if (obj is KeyValuePairComparer other)
                {
                    // Commonly, both comparers will be the default comparer (and reference-equal). Avoid a virtual method call to Equals() in that case.
                    return this.keyComparer == other.keyComparer || this.keyComparer.Equals(other.keyComparer);
                }
                return false;
            }

            public override int GetHashCode()
            {
                return this.keyComparer.GetHashCode();
            }
        }
    }

    /// <summary>
    /// This class is intended as a helper for backwards compatibility with existing SortedDictionaries.
    /// TreeSet has been converted into SortedSet{T}, which will be exposed publicly. SortedDictionaries
    /// have the problem where they have already been serialized to disk as having a backing class named
    /// TreeSet. To ensure that we can read back anything that has already been written to disk, we need to
    /// make sure that we have a class named TreeSet that does everything the way it used to.
    ///
    /// The only thing that makes it different from SortedSet is that it throws on duplicates
    /// </summary>
    /// <typeparam name="T"></typeparam>
    [Serializable]
    [System.Runtime.CompilerServices.TypeForwardedFrom("System, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089")]
    public sealed class TreeSet<T> : SortedSet<T>
    {
        [Ensures("@this.SpecItems.Length == 0")]
        [Ensures("@this.SpecComparer == Comparer<T>.Default")]
        public TreeSet()
        { }

        [Ensures("@this.SpecItems.Length == 0")]
        [Ensures("@this.SpecComparer == (comparer == null ? Comparer<T>.Default : comparer)")]
        public TreeSet(IComparer<T>? comparer) : base(comparer) { }

        internal TreeSet(TreeSet<T> set, IComparer<T>? comparer) : base(set, comparer) { }

        [Obsolete(Obsoletions.LegacyFormatterImplMessage, DiagnosticId = Obsoletions.LegacyFormatterImplDiagId, UrlFormat = Obsoletions.SharedUrlFormat)]
        private TreeSet(SerializationInfo siInfo, StreamingContext context) : base(siInfo, context) { }

        [Requires("@this.SpecItems.Length < int.MaxValue")]
        [Ensures("Result")]
        [Ensures("Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item) < 0")]
        [Ensures("@this.SpecItems == SpecTopDown.Inserted(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecItems), item)")]
        [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
        [Throws(typeof(ArgumentException), "Pal.KeyIndex(@this.SpecComparer, @this.SpecItems, item) >= 0")]
        internal override bool AddIfNotPresent(T item)
        {
            bool ret = base.AddIfNotPresent(item);
            if (!ret)
            {
                throw new ArgumentException(SR.Format(SR.Argument_AddingDuplicate, item));
            }
            return ret;
        }
    }
}
