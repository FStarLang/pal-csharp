using System;
using System.Diagnostics.CodeAnalysis;
using PalLang;

namespace System.Collections
{
    // R33.1. System.Collections' polyfill of the BCL's argument guards.
    internal static class ThrowHelper
    {
        internal static void ThrowIfNegative(int value, string? paramName = null)
        {
            if (value < 0) throw new ArgumentOutOfRangeException(paramName);
        }

        [DoesNotReturn]
        [Throws(typeof(InvalidOperationException))]
        [Ensures("false")]
        internal static void ThrowCycle() => throw new InvalidOperationException();
    }
}
