// EXPECT-PULSE: Failed to prove: FStar.Int32.v (FStar.Seq.Base.index var_s (FStar.Int32.v var_i)) == 0
// R4.7. A `[Lemma]` is a proof obligation, not a declaration. This is the case that says so,
// and it is the most load-bearing one in the directory: if a lemma's body were admitted
// rather than checked, every other proof in the system would rest on whatever its author
// happened to assert, and none of the cases here would mean anything.
//
// `AlwaysZero` claims that any element of any sequence, at any index in range, is zero. It
// has no `[PulseBody]`, so the proof offered is the empty one -- which is the right proof
// for a lemma that follows by computation, and no proof at all for this one.
using System.Diagnostics;
using PalLang;

public static class LemmaNotProved
{
    [Lemma]
    [Requires("0 <= i && i < s.Length")]
    [Ensures("s[i] == 0")]
    [Conditional("PAL")]
    // MARKER
    public static void AlwaysZero(Seq<int> s, int i) { }
}
