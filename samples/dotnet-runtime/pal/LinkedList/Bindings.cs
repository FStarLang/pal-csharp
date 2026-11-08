// R29.4, as in pal/Stack: the shared empty enumerator LinkedList<T>'s boxed enumerator returns.
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.EnumerableHelpers.GetEmptyEnumerator``1", "Pulse.Lib.CSharp.Obj.empty_enumerator")]

// R21.5 bindings of the BCL equality members Find and FindLast call (doc/translation.md §24,
// Pulse.Lib.CSharp.Equality), as in pal/HashCommon. Each is a modeling axiom.
[assembly: PalLang.SpecBinding("T:System.Collections.Generic.EqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]
[assembly: PalLang.SpecBinding("P:System.Collections.Generic.EqualityComparer`1.Default", "Pulse.Lib.CSharp.Equality.default_comparer")]
[assembly: PalLang.SpecBinding("M:System.Collections.Generic.EqualityComparer`1.Equals(`0,`0)", "Pulse.Lib.CSharp.Equality.equals")]
