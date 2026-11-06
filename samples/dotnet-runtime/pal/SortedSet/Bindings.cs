// R21.5. BitOperations.Log2 is floor(log2 x), and 0 at 0: a trusted binding.
[assembly: PalLang.SpecBinding("M:System.Numerics.BitOperations.Log2(System.UInt32)", "Pulse.Lib.CSharp.Arith.log2_u32")]
// R29.4, as in pal/Stack: the shared empty enumerator Stack<T>'s boxed enumerator returns.
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.EnumerableHelpers.GetEmptyEnumerator``1", "Pulse.Lib.CSharp.Obj.empty_enumerator")]
