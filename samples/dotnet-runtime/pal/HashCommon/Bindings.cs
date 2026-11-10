using PalLang;

// R21.5 bindings of the BCL equality members the hashing collections call
// (doc/translation.md §24, Pulse.Lib.CSharp.Equality). Each is a modeling axiom.
[assembly: SpecBinding("T:System.Collections.Generic.IEqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]
[assembly: SpecBinding("M:System.Collections.Generic.IEqualityComparer`1.Equals(`0,`0)", "Pulse.Lib.CSharp.Equality.equals")]
[assembly: SpecBinding("M:System.Collections.Generic.IEqualityComparer`1.GetHashCode(`0)", "Pulse.Lib.CSharp.Equality.get_hash_code")]
[assembly: SpecBinding("T:System.Collections.Generic.EqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]
[assembly: SpecBinding("P:System.Collections.Generic.EqualityComparer`1.Default", "Pulse.Lib.CSharp.Equality.default_comparer")]
[assembly: SpecBinding("M:System.Collections.Generic.EqualityComparer`1.Equals(`0,`0)", "Pulse.Lib.CSharp.Equality.equals")]
[assembly: SpecBinding("M:System.Collections.Generic.EqualityComparer`1.GetHashCode(`0)", "Pulse.Lib.CSharp.Equality.get_hash_code")]
[assembly: SpecBinding("M:System.Object.GetHashCode", "Pulse.Lib.CSharp.Equality.object_get_hash_code")]
[assembly: SpecBinding("T:System.Type", "Pulse.Lib.CSharp.Equality.type_handle")]
[assembly: SpecBinding("P:System.Type.IsValueType", "Pulse.Lib.CSharp.Equality.is_value_type")]

// R30.5. The table sizes (Pulse.Lib.CSharp.HashSize): trusted contracts, not verified bodies.
[assembly: SpecBinding("M:System.Collections.HashHelpers.GetPrime(System.Int32)", "Pulse.Lib.CSharp.HashSize.get_prime")]
[assembly: SpecBinding("M:System.Collections.HashHelpers.GetPrimeAtLeast(System.Int32)", "Pulse.Lib.CSharp.HashSize.get_prime_at_least")]
[assembly: SpecBinding("M:System.Collections.HashHelpers.IsPrime(System.Int32)", "Pulse.Lib.CSharp.HashSize.is_prime")]

// R30.6. The string comparer CoreLib picks for a string-keyed set or dictionary
// (Pulse.Lib.CSharp.StringComparers): a test for it, and its randomized counterpart, which
// has the same equality.
[assembly: SpecBinding("T:System.Collections.Generic.NonRandomizedStringEqualityComparer", "Pulse.Lib.CSharp.Equality.handle")]
[assembly: SpecBinding("is:T:System.Collections.Generic.NonRandomizedStringEqualityComparer", "Pulse.Lib.CSharp.StringComparers.is_non_randomized")]
[assembly: SpecBinding("M:System.Collections.Generic.NonRandomizedStringEqualityComparer.GetRandomizedEqualityComparer", "Pulse.Lib.CSharp.StringComparers.randomized")]
// R30.18. `NonRandomizedStringEqualityComparer.GetStringComparer(comparer)`: the
// non-randomized comparer with `comparer`'s equality, or null.
[assembly: SpecBinding("M:System.Collections.Generic.NonRandomizedStringEqualityComparer.GetStringComparer(System.Object)", "Pulse.Lib.CSharp.StringComparerOf.string_comparer")]
// R30.34. `IInternalStringEqualityComparer.GetUnderlyingEqualityComparer(comparer)`: the
// public comparer a string-keyed collection's `Comparer` returns, with `comparer`'s equality.
[assembly: SpecBinding("T:System.Collections.Generic.IInternalStringEqualityComparer", "Pulse.Lib.CSharp.Equality.handle")]
[assembly: SpecBinding("M:System.Collections.Generic.IInternalStringEqualityComparer.GetUnderlyingEqualityComparer(System.Collections.Generic.IEqualityComparer{System.String})", "Pulse.Lib.CSharp.StringUnderlying.underlying")]
