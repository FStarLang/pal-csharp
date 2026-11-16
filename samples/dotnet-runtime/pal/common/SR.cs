namespace System
{
    // Stands in for the generated resource class of CoreLib and System.Collections:
    // pal-csharp does not model exception messages (R21.7), so each is a constant.
    // A unit with a resource class of its own declares it, and its declaration is the one
    // its code binds to.
    internal static class SR
    {
        internal const string Arg_HTCapacityOverflow = "Arg_HTCapacityOverflow";
        internal const string Arg_NonZeroLowerBound = "Arg_NonZeroLowerBound";
        internal const string Arg_RankMultiDimNotSupported = "Arg_RankMultiDimNotSupported";
        internal const string Argument_AddingDuplicateWithKey = "Argument_AddingDuplicateWithKey";
        internal const string Argument_IncompatibleArrayType = "Argument_IncompatibleArrayType";
        internal const string Argument_InvalidOffLen = "Argument_InvalidOffLen";
        internal const string ArgumentOutOfRange_IndexMustBeLessOrEqual = "ArgumentOutOfRange_IndexMustBeLessOrEqual";
        internal const string InvalidOperation_EmptyQueue = "InvalidOperation_EmptyQueue";
        internal const string InvalidOperation_EmptyStack = "InvalidOperation_EmptyStack";
        internal const string InvalidOperation_EnumEnded = "InvalidOperation_EnumEnded";
        internal const string InvalidOperation_EnumFailedVersion = "InvalidOperation_EnumFailedVersion";
        internal const string InvalidOperation_EnumNotStarted = "InvalidOperation_EnumNotStarted";

        internal static string Format(string format, object? arg0) => format;
    }
}
