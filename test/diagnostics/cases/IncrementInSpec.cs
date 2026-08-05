// EXPECT: PALCS0576
// R13.3. An increment is a statement wearing an expression's clothes: it denotes a value,
// but it also writes. A specification denotes a state and never changes one, so there is
// no state for the write to land in and no translation to give it. The refusal is a
// translatability one — the specification the user meant is `k + 1`, and writing that is
// both shorter and what the annotation already means.
using PalLang;

public static class Stepping
{
    [Requires("0 <= k && k < 2147483646")]
    [Ensures("Result == k++")]
    public static int Next(int k)
    {
        return k + 1;
    }
}
