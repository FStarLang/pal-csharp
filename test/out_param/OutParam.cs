using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// `out` parameters. C#'s definite-assignment rules already guarantee the callee
/// writes every `out` parameter before returning, so the translation gives each
/// one a `pts_to` in the postcondition and the specification may talk about it
/// exactly as it would about a returned value.
/// </summary>
public static class OutParams
{
    [Ensures("q * d + r == n")]
    [Ensures("0 <= r && r < d")]
    [Requires("0 <= n && 0 < d")]
    public static void DivMod(int n, int d, out int q, out int r)
    {
        q = n / d;
        r = n - q * d;
    }

    [Ensures("lo == (x < y ? x : y)")]
    [Ensures("hi == (x < y ? y : x)")]
    public static void MinMax(int x, int y, out int lo, out int hi)
    {
        if (x < y)
        {
            lo = x;
            hi = y;
        }
        else
        {
            lo = y;
            hi = x;
        }
    }
}
