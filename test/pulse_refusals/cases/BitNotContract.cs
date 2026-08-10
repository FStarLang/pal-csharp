// EXPECT-PULSE: lognot
// R6.4b, at a unary operator. The binary table's catch-all emitted `+` for every
// operator it did not recognise (`test/pulse_refusals/cases/BitAndContract.cs`). The
// *unary* table had the same shape and did something quieter and worse: its catch-all
// returned the operand with the operator **dropped**.
//
// So `~e` in a specification meant `e`. This contract says `Result == ~(x + 1)`, which in
// C# is `-(x + 2)` — at `x == 7` it claims `Result == -9`. It reached F* as
// `Result == x + 1`, which the body satisfies, and it was proved.
//
// The shape matters. `~x` alone was ill-typed downstream, because the dropped operand was
// still an `I32.t` where a mathematical `int` was wanted, so the simplest probe of this
// hole produced an F* type error and looked like a translator limitation. It is only when
// the operand is *already* a mathematical term — as it is under any arithmetic, here
// `x + 1` — that the emission typechecks and the false theorem goes through.
//
// The refusal names `lognot`, the specification's complement.
using PalLang;

public static class BitNotContract
{
    [Requires("x > 0 && x < 100")]
    [Ensures("Result == ~(x + 1)")]
    public static int NotPlus(int x)
    {
        // MARKER
        return x + 1;
    }
}
