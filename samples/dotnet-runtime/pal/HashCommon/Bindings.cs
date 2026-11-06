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
