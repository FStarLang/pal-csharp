using Acme.Sdk;
using PalLang;

// R21.5a, R21.5b. A call into a library that is not part of the compilation. The library
// is referenced as metadata (`palcs -r`, see the Makefile), so Roslyn resolves `Tiers.Rate`
// to the overload the production build calls, and the binding below gives exactly that
// overload a model. The model is the trusted part: it says the library computes this
// function.
//
// The model comes in two readings, because a binding is applied at machine integers in
// code and a contract reads `int` as a mathematical integer (R20.10). `rate` is the
// function; `rate_i32` is the binding, defined from it, so the two cannot disagree.
// Contracts reach `rate` through the `[Spec]` mirror `AcmePricing.Rate`.
[assembly: IncludePulse("AcmeModel", """
module AcmeModel
module I32 = FStar.Int32

let rate (units: int) : r: int { 8 <= r /\ r <= 10 } =
  if units >= 100 then 8 else if units >= 10 then 9 else 10

let rate_i32 (units: I32.t) : I32.t = I32.int_to_t (rate (I32.v units))

let echo (#a: Type0) (value: a) : a = value
let is_missing (value: option bool) : bool =
  match value with | None -> true | Some _ -> false
""")]
[assembly: SpecBinding("M:Acme.Sdk.Tiers.Rate(System.Int32)", "AcmeModel.rate_i32")]
[assembly: SpecBinding("M:Acme.Sdk.Tiers.RateFor(System.Int32)", "AcmeModel.rate_i32")]
[assembly: SpecBinding("M:Acme.Sdk.Tiers.Echo``1(``0)", "AcmeModel.echo")]
[assembly: SpecBinding("M:Acme.Sdk.Tiers.IsMissing(System.Nullable{System.Boolean})", "AcmeModel.is_missing")]

namespace PalCSharp.Tests;

/// <summary>The specification reading of <c>Acme.Sdk.Tiers.Rate</c>.</summary>
public static class AcmePricing
{
    [Spec]
    [PulseBody("AcmeModel.rate $(units)")]
    public static SpecInt Rate(SpecInt units) => throw new System.InvalidOperationException();
}

public static class Quote
{
    [Requires("0 <= units && units <= 1000000")]
    [Ensures("Result == units * AcmePricing.Rate(units)")]
    [Ensures("Result <= 10 * units")]
    public static int Total(int units)
    {
        int rate = units.RateFor();
        return units * rate;
    }

    [Requires("0 <= units && units <= 1000000")]
    [Ensures("Result == (units >= 10)")]
    public static bool Discounted(int units) => Tiers.Rate(units) < 10;

    [Ensures("Result == value")]
    [Ensures("Result == value.Echo()")]
    public static bool Echo(bool value) => value.Echo();

    [Ensures("Result == (value == null)")]
    public static bool Missing(bool? value) => value.IsMissing();
}
