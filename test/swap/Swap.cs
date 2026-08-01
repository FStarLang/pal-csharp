using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The smallest interesting proof: two `ref` parameters, and a postcondition that
/// can only be stated by referring to the pre-state.
/// </summary>
public static class Swapping
{
    [Ensures("x == Old(y)")]
    [Ensures("y == Old(x)")]
    public static void Swap(ref int x, ref int y)
    {
        int t = x;
        x = y;
        y = t;
    }
}
