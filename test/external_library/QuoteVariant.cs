using Acme.Sdk;
using PalLang;

namespace PalCSharp.Tests;

/// <summary>The same contracts as <c>Quote</c>, written differently.</summary>
public static class QuoteVariant
{
    [Requires("0 <= units && units <= 1000000")]
    [Ensures("Result == units * AcmePricing.Rate(units)")]
    [Ensures("Result <= 10 * units")]
    public static int Total(int units)
    {
        if (units == 0) { return 0; }
        return Tiers.RateFor(units) * units;
    }

    [Requires("0 <= units && units <= 1000000")]
    [Ensures("Result == (units >= 10)")]
    public static bool Discounted(int units)
    {
        int full = Tiers.Rate(0);
        return Tiers.Rate(units) != full;
    }

    [Ensures("Result == value")]
    [Ensures("Result == Tiers.Echo(value)")]
    public static bool Echo(bool value) => Tiers.Echo(value);

    [Ensures("Result == (value == null)")]
    public static bool Missing(bool? value) => Tiers.IsMissing(value);
}
