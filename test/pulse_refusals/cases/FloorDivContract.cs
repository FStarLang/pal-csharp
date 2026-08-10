// EXPECT-PULSE: CA.cdiv
// R6.4a. A specification's `/` is C#'s, and this is the program that shows why it has
// to be. `Half` computes *floor* division — for negative odd `x` it rounds down, so
// `Half(-7)` is `-4` while C#'s `(-7) / 2` is `-3`. Its contract says `Result == x / 2`.
// Read as C#, by the person who wrote it, that claim is false.
//
// It used to be provable. The emitter sent a specification's `/` to F*'s `/`, which
// rounds toward minus infinity, so the contract meant floor division and the method
// computed floor division and the proof went through. The C# it was a theorem about
// returned a different number, and nothing in the pipeline was in a position to notice:
// both readings are spelled `x / 2`, and they part company only at a sign.
//
// The refusal names `CA.cdiv`, which is the specification's division — the obligation is
// that the floor division the method performs equals the truncating division the
// contract asks for, and at `x == -7` it does not.
using PalLang;

public static class FloorDivContract
{
    [Requires("x > -1000 && x < 1000")]
    [Ensures("Result == x / 2")]
    public static int Half(int x)
    {
        if (x >= 0)
        {
            return x / 2;
        }

        // MARKER
        return (x - 1) / 2;
    }
}
