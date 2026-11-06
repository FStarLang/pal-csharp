using System.Collections.Generic;

namespace System
{
    // Stands in for CoreLib's enumerator over an empty array.
    internal sealed class SZGenericArrayEnumerator<T> : IEnumerator<T>
    {
        internal static readonly SZGenericArrayEnumerator<T> Empty = new();
        public T Current => throw new InvalidOperationException();
        object? Collections.IEnumerator.Current => Current;
        public bool MoveNext() => false;
        public void Reset() { }
        public void Dispose() { }
    }
}

namespace System.Collections.Generic
{
    // Stand-ins for CoreLib internals that verified code does not reach.
    internal sealed class ICollectionDebugView<T>(ICollection<T> collection)
    {
        public ICollection<T> Collection => collection;
    }

    internal sealed class ArraySortHelper<T>
    {
        public static void Sort(Span<T> keys, Comparison<T> comparer) => throw new NotSupportedException();
        public static void Sort(Span<T> keys, IComparer<T>? comparer) => throw new NotSupportedException();
    }
}
