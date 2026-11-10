// R21.5. BitOperations.Log2 is floor(log2 x), and 0 at 0: a trusted binding.
[assembly: PalLang.SpecBinding("M:System.Numerics.BitOperations.Log2(System.UInt32)", "Pulse.Lib.CSharp.Arith.log2_u32")]
// R29.4, as in pal/Stack: the shared empty enumerator Stack<T>'s boxed enumerator returns.
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.EnumerableHelpers.GetEmptyEnumerator``1", "Pulse.Lib.CSharp.Obj.empty_enumerator")]
// R27.58. SortedDictionary's KeyValuePairComparer is a pair comparer comparing keys only: a
// trusted model (Pulse.Lib.CSharp.KeyComparer).
[assembly: PalLang.SpecBinding("T:System.Collections.Generic.SortedDictionary`2.KeyValuePairComparer", "Pulse.Lib.CSharp.KeyComparer.pair_comparer")]
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.SortedDictionary`2.KeyValuePairComparer.#ctor(System.Collections.Generic.IComparer{`0})", "Pulse.Lib.CSharp.KeyComparer.create")]
// R32.3. `EqualityComparer<T>.Default.Equals`, as the hashing harness binds it (R22.25's `default_equals`).
[assembly: PalLang.SpecBinding("T:System.Collections.Generic.EqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]
[assembly: PalLang.SpecBinding("P:System.Collections.Generic.EqualityComparer`1.Default", "Pulse.Lib.CSharp.Equality.default_comparer")]
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.EqualityComparer`1.Equals(`0,`0)", "Pulse.Lib.CSharp.Equality.equals")]
// R32.7. `KeyValuePairComparer.keyComparer` is the key comparer `key_of` recovers from the pair comparer.
[assembly: PalLang.SpecBinding("F:System.Collections.Generic.SortedDictionary`2.KeyValuePairComparer.keyComparer", "Pulse.Lib.CSharp.KeyComparer.key_of")]
