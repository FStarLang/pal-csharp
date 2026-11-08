using System.Collections.Generic;

// R29.4 binding of the shared empty enumerator (doc/translation.md R29.4, Pulse.Lib.CSharp.Obj).
// A modeling axiom: the call has no effect and does not throw.
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.EnumerableHelpers.GetEmptyEnumerator``1", "Pulse.Lib.CSharp.Obj.empty_enumerator")]

// R33.4: `IntPtr.Size` is an unknown constant (Pulse.Lib.CSharp.Platform). A modeling axiom.
[assembly: PalLang.SpecBinding("P:System.IntPtr.Size", "Pulse.Lib.CSharp.Platform.intptr_size")]

namespace System
{
    // Stands in for System.Collections' generated resource class. Messages are not
    // modelled (doc/translation.md R21.7, R25.1), so the strings are placeholders.
    internal static class SR
    {
        internal static string Arg_ArrayPlusOffTooSmall => nameof(Arg_ArrayPlusOffTooSmall);
        internal static string Arg_HTCapacityOverflow => nameof(Arg_HTCapacityOverflow);
        internal static string Arg_KeyNotFoundWithKey => nameof(Arg_KeyNotFoundWithKey);
        internal static string Arg_NonZeroLowerBound => nameof(Arg_NonZeroLowerBound);
        internal static string Arg_RankMultiDimNotSupported => nameof(Arg_RankMultiDimNotSupported);
        internal static string Arg_WrongType => nameof(Arg_WrongType);
        internal static string Argument_AddingDuplicate => nameof(Argument_AddingDuplicate);
        internal static string Argument_IncompatibleArrayType => nameof(Argument_IncompatibleArrayType);
        internal static string ArgumentOutOfRange_Generic_MustBeNonNegative => nameof(ArgumentOutOfRange_Generic_MustBeNonNegative);
        internal static string ArgumentOutOfRange_Generic_MustBeLessOrEqual => nameof(ArgumentOutOfRange_Generic_MustBeLessOrEqual);
        internal static string ArgumentOutOfRange_Generic_MustBeGreaterOrEqual => nameof(ArgumentOutOfRange_Generic_MustBeGreaterOrEqual);
        internal static string InvalidOperation_ConcurrentOperationsNotSupported => nameof(InvalidOperation_ConcurrentOperationsNotSupported);
        internal static string InvalidOperation_EnumFailedVersion => nameof(InvalidOperation_EnumFailedVersion);

        internal static string Format(string format, object? arg0) => format;
        internal static string Format(string format, object? arg0, object? arg1) => format;
        internal static string Format(string format, object? arg0, object? arg1, object? arg2) => format;
    }
}

namespace System.Collections.Generic
{
    // Stand-ins for System.Collections internals that verified code does not reach.
    internal static class EnumerableHelpers
    {
        internal static IEnumerator<T> GetEmptyEnumerator<T>() => ((IEnumerable<T>)Array.Empty<T>()).GetEnumerator();
        internal static void Reset<T>(ref T enumerator) where T : IEnumerator => enumerator.Reset();
    }
}
