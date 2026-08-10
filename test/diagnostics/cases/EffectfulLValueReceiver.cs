// EXPECT: PALCS0578
// R5.3. `x op= e` and `x++` are notations for `x = x op e`, and that expansion names the
// L-value twice. C# evaluates it exactly once, so an L-value with an effect in it is a
// program the expansion cannot express: the index of an element can be hoisted into a
// local and shared, but the *array* cannot — hoisting a resource is a move, not a
// binding. So this one is refused rather than translated into a program that allocates
// twice.
using PalLang;

public static class EffectfulLValueReceiver
{
    public static int[] Make() => new int[4];

    public static void Bad()
    {
        Make()[0] += 1;
    }
}
