using System.Diagnostics;
using PalLang;

namespace System.Collections;

// Stands in for the members of src/libraries/Common/src/System/Collections/HashHelpers.cs
// that OrderedDictionary<TKey,TValue> calls (doc/translation.md R33.5). That file is shared
// with the other hashing harnesses, so it is left as it is and not compiled here.
//
// * `ExpandPrime` and `GetFastModMultiplier` are copies of the real bodies, and are verified.
// * `GetPrime` and `FastMod` are TRUSTED: the contract is what is assumed of the real method,
//   and the body here only shows that it can be met.
internal static partial class HashHelpers
{
    public const uint HashCollisionThreshold = 100;

    // This is the maximum prime smaller than Array.MaxLength.
    public const int MaxPrimeArrayLength = 0x7FFFFFC3;

    public const int HashPrime = 101;

    /// <summary>
    /// TRUSTED. The real method returns the least prime `p >= min` (and `>= 3`) with
    /// `(p - 1) % HashPrime != 0`, from a table or by trial division. Both
    /// `MaxPrimeArrayLength` and `int.MaxValue` are such primes, so the search ends at or below
    /// the first of them that is `>= min`. A negative `min` throws.
    /// </summary>
    [Throws(typeof(ArgumentException), "min < 0")]
    [Ensures("min >= 0 && Result >= min && Result >= 3")]
    [Ensures("Implies(min <= HashHelpers.MaxPrimeArrayLength, Result <= HashHelpers.MaxPrimeArrayLength)")]
    public static int GetPrime(int min)
    {
        if (min < 0)
        {
            throw new ArgumentException();
        }
        return min <= 3 ? 3 : min;
    }

    /// <summary>Returns size of hashtable to grow to.</summary>
    [Wrapping]
    [Throws(typeof(ArgumentException), "oldSize >= HashHelpers.MaxPrimeArrayLength")]
    [Ensures("Implies(0 <= oldSize && oldSize < HashHelpers.MaxPrimeArrayLength, oldSize < Result && Result <= HashHelpers.MaxPrimeArrayLength)")]
    [Ensures("Implies(0 <= oldSize, oldSize < HashHelpers.MaxPrimeArrayLength)")]
    public static int ExpandPrime(int oldSize)
    {
        int newSize = 2 * oldSize;

        // Allow the hashtables to grow to maximum possible size (~2G elements) before encountering capacity overflow.
        // Note that this check works even when _items.Length overflowed thanks to the (uint) cast
        if ((uint)newSize > MaxPrimeArrayLength && MaxPrimeArrayLength > oldSize)
        {
            Debug.Assert(MaxPrimeArrayLength == GetPrime(MaxPrimeArrayLength), "Invalid MaxPrimeArrayLength");
            return MaxPrimeArrayLength;
        }

        return GetPrime(newSize);
    }

    /// <summary>`ulong.MaxValue / divisor + 1`, as a specification.</summary>
    [Spec]
    [PulseBody("OrderedDictionaryChain.multiplier $(divisor)")]
    public static ulong Multiplier(uint divisor) => throw new InvalidOperationException();

    /// <summary>Returns approximate reciprocal of the divisor: ceil(2**64 / divisor).</summary>
    /// <remarks>This should only be used on 64-bit.</remarks>
    [Wrapping]
    [Requires("divisor > 0")]
    [Ensures("Result == HashHelpers.Multiplier(divisor)")]
    public static ulong GetFastModMultiplier(uint divisor) =>
        ulong.MaxValue / divisor + 1;

    /// <summary>
    /// TRUSTED. Performs a mod operation using the multiplier pre-computed with
    /// <see cref="GetFastModMultiplier"/>. The real body is
    /// `(uint)(((((multiplier * value) >> 32) + 1) * divisor) >> 32)`, which is
    /// `value % divisor` for `divisor <= int.MaxValue` (Lemire, Kaser and Kurz, "Faster
    /// remainder by direct computation", 2019); the BCL's own `Debug.Assert` says so.
    /// </summary>
    [Requires("0 < divisor && divisor <= int.MaxValue")]
    [Requires("multiplier == HashHelpers.Multiplier(divisor)")]
    [Ensures("Result == value % divisor")]
    public static uint FastMod(uint value, uint divisor, ulong multiplier) => value % divisor;
}
