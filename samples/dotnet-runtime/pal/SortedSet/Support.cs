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
        internal static string Arg_ArrayPlusOffTooSmall => nameof(Arg_ArrayPlusOffTooSmall);
        internal static string Arg_KeyNotFoundWithKey => nameof(Arg_KeyNotFoundWithKey);
        internal static string Arg_NonZeroLowerBound => nameof(Arg_NonZeroLowerBound);
        internal static string Arg_RankMultiDimNotSupported => nameof(Arg_RankMultiDimNotSupported);
        internal static string Arg_WrongType => nameof(Arg_WrongType);
        internal static string ArgumentOutOfRange_IndexMustBeLess => nameof(ArgumentOutOfRange_IndexMustBeLess);
        internal static string ArgumentOutOfRange_IndexMustBeLessOrEqual => nameof(ArgumentOutOfRange_IndexMustBeLessOrEqual);
        internal static string ArgumentOutOfRange_SmallCapacity => nameof(ArgumentOutOfRange_SmallCapacity);
        internal static string Argument_AddingDuplicate => nameof(Argument_AddingDuplicate);
        internal static string Argument_InvalidOffLen => nameof(Argument_InvalidOffLen);
        internal static string Argument_IncompatibleArrayType => nameof(Argument_IncompatibleArrayType);
        internal static string InvalidOperation_EnumFailedVersion => nameof(InvalidOperation_EnumFailedVersion);
        internal static string InvalidOperation_EnumOpCantHappen => nameof(InvalidOperation_EnumOpCantHappen);
        internal static string InvalidOperation_EmptyStack => nameof(InvalidOperation_EmptyStack);
        internal static string InvalidOperation_EmptyQueue => nameof(InvalidOperation_EmptyQueue);
        internal static string NotSupported_KeyCollectionSet => nameof(NotSupported_KeyCollectionSet);
        internal static string NotSupported_SortedListNestedWrite => nameof(NotSupported_SortedListNestedWrite);
        internal static string NotSupported_ValueCollectionSet => nameof(NotSupported_ValueCollectionSet);
        internal static string Serialization_InvalidOnDeser => nameof(Serialization_InvalidOnDeser);
        internal static string Serialization_MismatchedCount => nameof(Serialization_MismatchedCount);
        internal static string Serialization_MissingValues => nameof(Serialization_MissingValues);
        internal static string SortedSet_LowerValueGreaterThanUpperValue => nameof(SortedSet_LowerValueGreaterThanUpperValue);

        internal static string Format(string format, object? arg0) => format;
        internal static string Format(string format, object? arg0, object? arg1, object? arg2) => format;
        internal static string Format(string format, object? arg0, object? arg1) => format;
    }
}

namespace System.Collections.Generic
{
    internal sealed class IDictionaryDebugView<TKey, TValue>(IDictionary<TKey, TValue> dictionary)
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
}
