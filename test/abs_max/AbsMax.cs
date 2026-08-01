using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Branching and a value-returning method. `Result` names the returned value in a
/// postcondition, and the precondition is what rules out the one case C# cannot
/// negate: `int.MinValue`.
/// </summary>
public static class Arithmetic
{
    [Requires("x > int.MinValue")]
    [Ensures("Result >= 0")]
    [Ensures("Result == x || Result == 0 - x")]
    public static int Abs(int x)
    {
        if (x < 0)
        {
            return 0 - x;
        }
        return x;
    }

    [Ensures("Result >= x && Result >= y")]
    [Ensures("Result == x || Result == y")]
    public static int Max(int x, int y)
    {
        if (x < y)
        {
            return y;
        }
        return x;
    }
}
