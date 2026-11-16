using PalLang;

[assembly: TranslateAnnotatedOnly]

namespace PalCSharp.Tests;

/// <summary>A unit translated with only its annotated members (R20.1).</summary>
public static class Picked
{
    [Ensures("Result == x")]
    public static int Same(int x)
    {
        return x;
    }
}
