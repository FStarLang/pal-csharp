// EXPECT: PALCS0001
// R6.4b. A shift in specification position is refused rather than translated.
//
// C#'s `<<` masks its count: for an `int` the shift is by `count & 31`, so `x << 33` is
// `x << 1` (ECMA-334 §12.11). F*'s `shift_left` has no such rule — it carries a
// precondition on the count instead — so there is no F* term that means what C#'s `<<`
// means without the masking being written down, and no rule has been written for it.
//
// §0 rule 3 says what to do about that: refuse. The alternative is what this arm used to
// do, which was to fall through a catch-all and emit `+` — see
// `test/pulse_refusals/cases/BitAndContract.cs` for the false theorem that made possible.
// A refusal is incompleteness and can only reject a program; a wrong translation of a
// *specification* cannot be caught downstream at all, because the prover is checking the
// translation rather than the C#.
using PalLang;

public static class ShiftInSpec
{
    [Requires("shiftMe > 0 && shiftMe < 100")]
    [Ensures("Result == (shiftMe << 1)")]
    public static int Doubled(int shiftMe)
    {
        return shiftMe + shiftMe;
    }
}
