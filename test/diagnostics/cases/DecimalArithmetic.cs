// EXPECT: PALCS0624
using PalLang;

public static class DecimalArithmetic
{
    public static decimal Bad(decimal a, decimal b) => a + b;
}
