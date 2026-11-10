// R29.4 binding of the shared empty enumerator (doc/translation.md R29.4, Pulse.Lib.CSharp.Obj).
// A modeling axiom: the call has no effect and does not throw.
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.EnumerableHelpers.GetEmptyEnumerator``1", "Pulse.Lib.CSharp.Obj.empty_enumerator")]

// `typeof(TPriority).IsValueType` (InitializeComparer) and the equality comparers (FindIndex) are bound in ../HashCommon/Bindings.cs.

[assembly: PalLang.IncludePulseFile("PriorityQueueRemove.fst")]

namespace System
{
    // Stands in for System.Collections' resource strings.
    internal static class SR
    {
        internal const string InvalidOperation_EmptyQueue = "Queue empty.";
        internal const string ArgumentOutOfRange_IndexMustBeLessOrEqual = "Index must be less or equal.";
        internal const string Argument_IncompatibleArrayType = "Incompatible array type.";
        internal const string Argument_InvalidOffLen = "Invalid offset or length.";
        internal const string Argument_InvalidArrayType = "Target array type is not compatible with the type of items in the collection.";
        internal const string Arg_NonZeroLowerBound = "The lower bound of target array must be zero.";
        internal const string Arg_RankMultiDimNotSupported = "Only single dimensional arrays are supported for the requested action.";
        internal const string Arg_ArrayPlusOffTooSmall = "Destination array is not long enough to copy all the items in the collection. Check array index and length.";
        internal const string InvalidOperation_EnumFailedVersion = "Collection was modified; enumeration operation may not execute.";
        internal const string InvalidOperation_EnumOpCantHappen = "Enumeration has either not started or has already finished.";
    }
}

namespace System.Collections.Generic
{
    // Stand-ins for System.Collections internals that verified code does not reach.
    internal static class EnumerableHelpers
    {
        internal static T[] ToArray<T>(IEnumerable<T> source, out int length) => throw new NotSupportedException();
        internal static IEnumerator<T> GetEmptyEnumerator<T>() => throw new NotSupportedException();
    }

    internal sealed class PriorityQueueDebugView<TElement, TPriority>(PriorityQueue<TElement, TPriority> queue)
    {
        public int Count => queue.Count;
    }
}