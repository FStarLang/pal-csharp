namespace Acme.Sdk;

/// <summary>
/// A vendor's pricing table. pal-csharp never sees this source: the verified program is
/// translated against the compiled assembly, so what it binds to is what ships.
/// </summary>
public static class Tiers
{
    /// <summary>The unit price for an order of <paramref name="units"/>.</summary>
    public static int Rate(int units) => units >= 100 ? 8 : units >= 10 ? 9 : 10;

    /// <summary>
    /// An overload with a different meaning. A binding names one overload exactly, so this
    /// one stays unmodelled, and a verified call to it is refused.
    /// </summary>
    public static int Rate(int units, int loyaltyYears) => Rate(units) - (loyaltyYears >= 5 ? 1 : 0);

    public static int RateFor(this int units) => Rate(units);

    public static T Echo<T>(this T value) => value;

    public static bool IsMissing(this bool? value) => value is null;
}

public static class Windows
{
    public static System.Span<int> AsSpan(this int[] array) => new(array, 0, 0);
}
