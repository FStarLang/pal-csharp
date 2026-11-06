using PalLang;

namespace System;

// Stands in for CoreLib's ThrowHelper (src/libraries/System.Private.CoreLib/src/System/
// ThrowHelper.cs), whose bodies build messages from resources pal-csharp does not model.
// Each method has the real signature and throws the real exception class, and, like the
// real one, never returns: `[Ensures("false")]` is `[DoesNotReturn]` stated as a contract.
// That each stand-in throws the class its original throws is a trusted fact (see README).
internal static class ThrowHelper
{
    [DoesNotReturn]
    [Throws(typeof(ArgumentException))]
    [Ensures("false")]
    internal static void ThrowArgumentException(ExceptionResource resource) => throw new ArgumentException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentException))]
    [Ensures("false")]
    internal static void ThrowArgumentException(ExceptionResource resource, ExceptionArgument argument) => throw new ArgumentException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentException))]
    [Ensures("false")]
    internal static void ThrowArgumentException_Argument_IncompatibleArrayType() => throw new ArgumentException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentNullException))]
    [Ensures("false")]
    internal static void ThrowArgumentNullException(ExceptionArgument argument) => throw new ArgumentNullException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowArgumentOutOfRangeException() => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowArgumentOutOfRangeException(ExceptionArgument argument) => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowArgumentOutOfRangeException(ExceptionArgument argument, ExceptionResource resource) => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowArgumentOutOfRange_IndexMustBeLessException() => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowArgumentOutOfRange_IndexMustBeLessOrEqualException() => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowCountArgumentOutOfRange_ArgumentOutOfRange_Count() => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowIndexArgumentOutOfRange_NeedNonNegNumException() => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowStartIndexArgumentOutOfRange_ArgumentOutOfRange_IndexMustBeLess() => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(ArgumentOutOfRangeException))]
    [Ensures("false")]
    internal static void ThrowStartIndexArgumentOutOfRange_ArgumentOutOfRange_IndexMustBeLessOrEqual() => throw new ArgumentOutOfRangeException();

    [DoesNotReturn]
    [Throws(typeof(InvalidOperationException))]
    [Ensures("false")]
    internal static void ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion() => throw new InvalidOperationException();

    [DoesNotReturn]
    [Throws(typeof(InvalidOperationException))]
    [Ensures("false")]
    internal static void ThrowInvalidOperationException_InvalidOperation_EnumOpCantHappen() => throw new InvalidOperationException();

    // Not [DoesNotReturn]: throws only when `value` is null and `T` cannot be.
    internal static void IfNullAndNullsAreIllegalThenThrow<T>(object? value, ExceptionArgument argName)
    {
        if (!(default(T) == null) && value == null) throw new ArgumentNullException();
    }

    [DoesNotReturn]
    internal static void ThrowWrongValueTypeArgumentException<T>(T value, Type targetType) =>
        throw new ArgumentException();
}

internal enum ExceptionArgument
{
    action, capacity, collection, comparison, converter, count, index, item, match, value,
    startIndex, array, arrayIndex, comparer, key, list, length,
}

internal enum ExceptionResource
{
    Arg_RankMultiDimNotSupported, ArgumentOutOfRange_BiggerThanCollection,
    ArgumentOutOfRange_ListInsert, ArgumentOutOfRange_NeedNonNegNum,
    ArgumentOutOfRange_SmallCapacity, Argument_InvalidOffLen,
    Arg_NonZeroLowerBound, ArgumentOutOfRange_IndexMustBeLessOrEqual,
}
