using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Variant of <see cref="Arithmetic"/> (plan §7.2): the same two functions with the
/// same contracts, written differently — the branches are inverted, the returns are
/// structured rather than early, and the locals are named and ordered differently.
/// It must verify with no change to the translator. If it did not, the translator
/// would be fitted to the shape of the original rather than implementing the scheme.
/// </summary>
public static class ArithmeticVariant
{
    [Requires("x > int.MinValue")]
    [Ensures("Result >= 0")]
    [Ensures("Result == x || Result == 0 - x")]
    public static int Abs(int x)
    {
        int magnitude;
        if (x >= 0)
        {
            magnitude = x;
        }
        else
        {
            magnitude = 0 - x;
        }
        return magnitude;
    }

    [Ensures("Result >= x && Result >= y")]
    [Ensures("Result == x || Result == y")]
    public static int Max(int x, int y)
    {
        int larger = y;
        if (y <= x)
        {
            larger = x;
        }
        return larger;
    }
}
