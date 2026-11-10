// Stand-ins for CoreLib internals that Dictionary<TKey, TValue> names but verified code
// does not reach (debugger views) or reaches only through a binding (the shared empty
// enumerator). They exist only so that
// the sources compile.

// R29.4 binding of the shared empty enumerator, as pal/common/Bindings.cs binds
// SZGenericArrayEnumerator's: a modeling axiom (reading it has no effect and does not throw).
[assembly: PalLang.SpecBinding("F:System.Collections.Generic.GenericEmptyEnumerator`1.Instance", "Pulse.Lib.CSharp.Obj.empty_enumerator")]
[assembly: PalLang.SpecBinding("T:System.Collections.Generic.GenericEmptyEnumerator`1", "Pulse.Lib.CSharp.Obj.enumerator_of")]

namespace System.Collections.Generic
{
    internal sealed class IDictionaryDebugView<TKey, TValue>(IDictionary<TKey, TValue> dictionary) where TKey : notnull
    {
        public IDictionary<TKey, TValue> Dictionary => dictionary;
    }

    internal sealed class DictionaryKeyCollectionDebugView<TKey, TValue>(ICollection<TKey> collection)
    {
        public ICollection<TKey> Collection => collection;
    }

    internal sealed class DictionaryValueCollectionDebugView<TKey, TValue>(ICollection<TValue> collection)
    {
        public ICollection<TValue> Collection => collection;
    }

    internal sealed class GenericEmptyEnumerator<T> : IEnumerator<T>
    {
        public static readonly GenericEmptyEnumerator<T> Instance = new();
        public T Current => throw new InvalidOperationException();
        object? IEnumerator.Current => Current;
        public bool MoveNext() => false;
        public void Reset() { }
        public void Dispose() { }
    }
}
