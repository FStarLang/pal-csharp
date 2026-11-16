using PalLang;

namespace PalCSharp.Tests;

public static class ReferenceIdentity
{
    [Ensures("Result == ReferenceEquals(left, right)")]
    public static bool Equal<T>(Knot<T>? left, Knot<T>? right) => left == right;

    [Ensures("Result == !ReferenceEquals(left, right)")]
    public static bool Different<T>(Knot<T> left, Knot<T>? right) => left != right;
}
