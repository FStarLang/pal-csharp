// R21.5. BitOperations.Log2 is floor(log2 x), and 0 at 0: a trusted binding.
[assembly: PalLang.SpecBinding("M:System.Numerics.BitOperations.Log2(System.UInt32)", "Pulse.Lib.CSharp.Arith.log2_u32")]
// R29.4, as in pal/Stack: the shared empty enumerator Stack<T>'s boxed enumerator returns.
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.EnumerableHelpers.GetEmptyEnumerator``1", "Pulse.Lib.CSharp.Obj.empty_enumerator")]
// R27.58. SortedDictionary's KeyValuePairComparer is a pair comparer comparing keys only: a
// trusted model (Pulse.Lib.CSharp.KeyComparer).
[assembly: PalLang.SpecBinding("T:System.Collections.Generic.SortedDictionary`2.KeyValuePairComparer", "Pulse.Lib.CSharp.KeyComparer.pair_comparer")]
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.SortedDictionary`2.KeyValuePairComparer.#ctor(System.Collections.Generic.IComparer{`0})", "Pulse.Lib.CSharp.KeyComparer.create")]
