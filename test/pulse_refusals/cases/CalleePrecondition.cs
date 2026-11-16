// EXPECT-PULSE: Failed to prove pure property: ‘I32.v var_n > 0
// R4.1. A call must establish the callee's precondition at the call site. `Half` demands a
// positive argument; `Caller` passes one it has not bounded, so the obligation lands on
// the call rather than inside `Half`, which is itself perfectly provable.
using PalLang;

public static class CalleePrecondition
{
    [Requires("x > 0 && x < 1000")]
    [Ensures("Result >= 0")]
    public static int Half(int x) => x / 2;

    public static int Caller(int n)
    {
        // MARKER
        return Half(n);
    }
}
