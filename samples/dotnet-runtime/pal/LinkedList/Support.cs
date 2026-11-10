using System.Collections.Generic;

namespace System
{
    // Stands in for System.Collections' generated resource class. Messages are not
    // modelled (doc/translation.md R21.7, R25.1), so the strings are placeholders.
    internal static class Obsoletions
    {
        internal const string LegacyFormatterImplMessage = nameof(LegacyFormatterImplMessage);
        internal const string LegacyFormatterImplDiagId = nameof(LegacyFormatterImplDiagId);
        internal const string SharedUrlFormat = nameof(SharedUrlFormat);
    }

    internal static class SR
    {
        internal static string Arg_InsufficientSpace => nameof(Arg_InsufficientSpace);
        internal static string Arg_NonZeroLowerBound => nameof(Arg_NonZeroLowerBound);
        internal static string Arg_RankMultiDimNotSupported => nameof(Arg_RankMultiDimNotSupported);
        internal static string Argument_IncompatibleArrayType => nameof(Argument_IncompatibleArrayType);
        internal static string ArgumentOutOfRange_BiggerThanCollection => nameof(ArgumentOutOfRange_BiggerThanCollection);
        internal static string ExternalLinkedListNode => nameof(ExternalLinkedListNode);
        internal static string InvalidOperation_EnumFailedVersion => nameof(InvalidOperation_EnumFailedVersion);
        internal static string InvalidOperation_EnumOpCantHappen => nameof(InvalidOperation_EnumOpCantHappen);
        internal static string LinkedListEmpty => nameof(LinkedListEmpty);
        internal static string LinkedListNodeIsAttached => nameof(LinkedListNodeIsAttached);
        internal static string Serialization_MissingValues => nameof(Serialization_MissingValues);
    }
}

namespace System.Collections.Generic
{
    // Stand-ins for System.Collections internals that verified code does not reach.
    internal static class EnumerableHelpers
    {
        internal static IEnumerator<T> GetEmptyEnumerator<T>() => ((IEnumerable<T>)Array.Empty<T>()).GetEnumerator();
    }
}
