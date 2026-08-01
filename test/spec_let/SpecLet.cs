using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// `[Spec]` methods: pure definitions that exist only in specifications. They are the
/// C# analogue of PAL's `_let`, but written as real C# — so the C# compiler
/// typechecks them, and pal-csharp translates their bodies rather than pasting a
/// string.
/// </summary>
public static class Sums
{
    /// <summary>The closed form; a non-recursive definition over `SpecInt`.</summary>
    [Spec]
    [Requires("0 <= n")]
    public static SpecInt Gauss(SpecInt n) => n * (n + 1) / 2;

    /// <summary>The sum of the first `n` elements, defined by recursion.</summary>
    [Spec(Recursive = true)]
    [Requires("0 <= n && n <= s.Length")]
    [Decreases("n")]
    public static SpecInt SumUpTo(Seq<int> s, SpecInt n) =>
        n == 0 ? 0 : SumUpTo(s, n - 1) + s[n - 1];
}
