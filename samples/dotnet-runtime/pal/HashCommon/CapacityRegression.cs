using System;
using PalLang;

namespace System.Collections
{
    internal static class CapacityRegression
    {
        [Requires("min >= 0")]
        [Ensures("Result >= min && HashHelpers.PrimeSize(Result)")]
        internal static int NonnegativePrime(int min) =>
            HashHelpers.GetPrime(min);

        [Requires("min < 0")]
        [Ensures("false")]
        [Throws(typeof(ArgumentException))]
        internal static void NegativePrimeThrows(int min) =>
            HashHelpers.GetPrime(min);

        [Ensures("Result == 0x7FFFFFC3")]
        internal static int GrowToMaximum() =>
            HashHelpers.ExpandPrime(0x7FFFFFC2);

        [Ensures("false")]
        [Throws(typeof(ArgumentException))]
        internal static void MaximumThrows() =>
            HashHelpers.ExpandPrime(0x7FFFFFC3);
    }
}
