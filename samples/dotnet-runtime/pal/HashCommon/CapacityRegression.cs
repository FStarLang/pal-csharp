using System;
using PalLang;

namespace System.Collections
{
    internal static class CapacityRegression
    {
        [Ensures("Result == 0x7FFFFFC3")]
        internal static int GrowToMaximum() =>
            HashHelpers.ExpandPrime(0x7FFFFFC2);

        [Ensures("false")]
        [Throws(typeof(ArgumentException))]
        internal static void MaximumThrows() =>
            HashHelpers.ExpandPrime(0x7FFFFFC3);
    }
}
