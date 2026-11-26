using PalLang;

// R30.5. Prime searches retain trusted contracts; GetPrime's negative-size guard is checked.
// Kept apart from Bindings.cs: OrderedDictionary and PriorityQueue include only that file, and
// OrderedDictionary verifies against its own HashHelpers copy rather than these bindings.
[assembly: SpecBinding("M:System.Collections.HashHelpers.GetPrime(System.Int32)", "Pulse.Lib.CSharp.HashSize.Checked.get_prime")]
[assembly: SpecBinding("M:System.Collections.HashHelpers.GetPrimeAtLeast(System.Int32)", "Pulse.Lib.CSharp.HashSize.get_prime_at_least")]
[assembly: SpecBinding("M:System.Collections.HashHelpers.IsPrime(System.Int32)", "Pulse.Lib.CSharp.HashSize.is_prime")]
