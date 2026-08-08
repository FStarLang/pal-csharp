// EXPECT: PALCS0501
// R18.3. R2.1 qualifies a module by the declaring *type*, not by its namespace, so
// `Alpha.Meter.Read` and `Beta.Meter.Read` both mangle to `Func_Meter_Read` and one would
// overwrite the other. R2.1a does not help: the two are not an overload set, because they
// are not members of one type.
//
// This is the case R2.1's own text admits it does not cover -- the qualifier is the
// smallest rule that keeps the mapping injective *within* a namespace. What matters is
// that the collision is reported rather than silently resolved in favour of whichever
// declaration the emitter reached second.
using PalLang;

namespace Alpha
{
    public static class Meter
    {
        [Ensures("Result == k")]
        public static int Read(int k) { return k; }
    }
}

namespace Beta
{
    public static class Meter
    {
        [Ensures("Result == 0 - k")]
        [Requires("k > -2147483648")]
        public static int Read(int k) { return -k; }
    }
}
