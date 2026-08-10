// EXPECT-PULSE: FStar.Int.size (FStar.Int32.v var_x + FStar.Int32.v var_y) 32
// R6.4. C# `int` addition is addition on a 32-bit machine integer, and the translation
// says so: the obligation is that the mathematical sum is representable. Unbounded
// parameters cannot discharge it.
using PalLang;

public static class SumOverflows
{
    public static int Add(int x, int y)
    {
        // MARKER
        return x + y;
    }
}
