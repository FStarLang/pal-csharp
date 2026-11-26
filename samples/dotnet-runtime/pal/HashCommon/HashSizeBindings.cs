using PalLang;

// R30.5. Prime searches retain trusted contracts; GetPrime's negative-size guard is checked.
// GetPrime uses [Implements] on its declaration so callers retain exception effects;
// a SpecBinding would incorrectly present this potentially throwing operation as pure.
// Kept apart from Bindings.cs: OrderedDictionary and PriorityQueue include only that file, and
// OrderedDictionary verifies against its own HashHelpers copy rather than these bindings.
[assembly: SpecBinding("M:System.Collections.HashHelpers.GetPrimeAtLeast(System.Int32)", "Pulse.Lib.CSharp.HashSize.get_prime_at_least")]
[assembly: SpecBinding("M:System.Collections.HashHelpers.IsPrime(System.Int32)", "Pulse.Lib.CSharp.HashSize.is_prime")]
