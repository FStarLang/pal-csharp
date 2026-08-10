// EXPECT-PULSE: FStar.Int32.v var_y <> 0
// R6.4. Division carries two obligations -- a non-zero divisor, and representability of
// the quotient, which for `int` fails only at `MinValue / -1`. Neither is discharged here.
using PalLang;

public static class DivisorNonZero
{
    public static int Ratio(int x, int y)
    {
        // MARKER
        return x / y;
    }
}
