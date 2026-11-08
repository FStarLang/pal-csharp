global using PalLang;
using PalLang;

// The definitions OrderedDictionary<TKey,TValue>'s specification is written in
// (doc/translation.md §33).
[assembly: IncludePulseFile("OrderedDictionaryChain.fst")]

namespace System.Collections.Generic
{
    /// <summary>The abstract state of an <see cref="OrderedDictionary{TKey, TValue}"/>.</summary>
    [Spec]
    public struct OrderedDictionaryModel<TKey, TValue>
    {
        public SpecInt Count;
        /// <summary>The keys, in order.</summary>
        public Seq<TKey> Keys;
        /// <summary>The values, in order: <c>Values[i]</c> is <c>Keys[i]</c>'s.</summary>
        public Seq<TValue> Values;
        /// <summary>The comparer the dictionary was built with; null means the default comparer.</summary>
        public IEqualityComparer<TKey>? Comparer;
        /// <summary>The modification counter an enumerator checks.</summary>
        public SpecInt Version;
        /// <summary>The number of pairs it can hold without resizing.</summary>
        public SpecInt Capacity;
    }
}
