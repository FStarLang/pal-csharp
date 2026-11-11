using PalLang;

// R30.5. The table sizes (Pulse.Lib.CSharp.HashSize): trusted contracts, not verified bodies.
// Kept apart from Bindings.cs: OrderedDictionary and PriorityQueue include only that file, and
// OrderedDictionary verifies against its own HashHelpers copy (whose GetPrime throws on a
// negative size, as the real one does) rather than these preconditioned contracts.
[assembly: SpecBinding("M:System.Collections.HashHelpers.GetPrime(System.Int32)", "Pulse.Lib.CSharp.HashSize.get_prime")]
[assembly: SpecBinding("M:System.Collections.HashHelpers.GetPrimeAtLeast(System.Int32)", "Pulse.Lib.CSharp.HashSize.get_prime_at_least")]
[assembly: SpecBinding("M:System.Collections.HashHelpers.IsPrime(System.Int32)", "Pulse.Lib.CSharp.HashSize.is_prime")]
