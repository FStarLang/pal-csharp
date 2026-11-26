namespace System
{
    // Only private resource/attribute infrastructure is substituted, not collection logic.
    internal static class SR
    {
        internal const string Arg_ArrayPlusOffTooSmall = nameof(Arg_ArrayPlusOffTooSmall);
        internal const string Arg_RankMultiDimNotSupported = nameof(Arg_RankMultiDimNotSupported);
        internal const string Arg_NonZeroLowerBound = nameof(Arg_NonZeroLowerBound);
        internal const string Argument_IncompatibleArrayType = nameof(Argument_IncompatibleArrayType);
        internal const string SortedSet_LowerValueGreaterThanUpperValue = nameof(SortedSet_LowerValueGreaterThanUpperValue);
        internal const string Serialization_InvalidOnDeser = nameof(Serialization_InvalidOnDeser);
        internal const string Serialization_MissingValues = nameof(Serialization_MissingValues);
        internal const string Serialization_MismatchedCount = nameof(Serialization_MismatchedCount);
        internal const string InvalidOperation_EnumFailedVersion = nameof(InvalidOperation_EnumFailedVersion);
        internal const string InvalidOperation_EnumOpCantHappen = nameof(InvalidOperation_EnumOpCantHappen);
    }

    internal static class Obsoletions
    {
        internal const string LegacyFormatterImplMessage = "Formatter-based serialization is obsolete.";
        internal const string LegacyFormatterImplDiagId = "SYSLIB0051";
        internal const string SharedUrlFormat = "https://aka.ms/dotnet-warnings/{0}";
    }
}

namespace System.Collections.Generic
{
    internal sealed class ICollectionDebugView<T>(ICollection<T> collection)
    {
        public T[] Items => collection.ToArray();
    }
}

namespace Xunit
{
    // A package-free runner for the exact proposed test method; not the xUnit framework.
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class TheoryAttribute : Attribute;

    [AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
    public sealed class InlineDataAttribute(params object[] arguments) : Attribute
    {
        public object[] Arguments { get; } = arguments;
    }

    public sealed class AssertionFailure(string message) : Exception(message);

    public static class Assert
    {
        public static void False(bool condition)
        {
            if (condition)
                throw new AssertionFailure("Expected false, got true.");
        }
    }
}
