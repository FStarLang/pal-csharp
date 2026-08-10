// EXPECT-PULSE: logand
// R6.4b. A specification's `&` is C#'s bitwise AND, and this is the program that shows
// why it has to be something rather than nothing.
//
// `x & 0` is `0` for every `x`. `AndZero` returns `x`, so its contract is false for
// every `x` the precondition admits — at `x == 7` it claims `7 == 0`.
//
// It used to be provable, and the mechanism was not a subtle disagreement about a
// rounding: `SpecEmitter.Binary` ended its operator table in a catch-all arm that
// returned `+`. Every operator it did not recognise — `&`, `|`, `^`, `<<`, `>>` — was
// emitted as *addition*. So this contract reached F* as `Result == x + 0`, which the
// body satisfies, and the proof went through. Running the C# prints `7` where the
// certificate said `0`.
//
// That is the same shape as R6.4a's floor division and strictly worse: `/` and F*'s `/`
// at least agree on most inputs, whereas `&` and `+` agree on almost none. A default
// arm answering for operators it does not know is how it happened, which is why R6.4b
// refuses rather than defaults.
//
// The refusal names `logand`, the specification's AND: the obligation is that the `x`
// the method returns equals `x & 0`, and it does not.
using PalLang;

public static class BitAndContract
{
    [Requires("x > 0 && x < 100")]
    [Ensures("Result == (x & 0)")]
    public static int AndZero(int x)
    {
        // MARKER
        return x;
    }
}
