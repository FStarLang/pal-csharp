using PalLang;

// The "external system" below is ordinary C#, outside the translation.
[assembly: TranslateAnnotatedOnly]

// R20.14. A model of an external system, verified in Pulse: a counter that only grows.
[assembly: IncludePulse("CounterModel", """
module CounterModel
#lang-pulse
open Pulse
module I32 = FStar.Int32

fn bump (x: I32.t)
  requires pure (0 <= I32.v x /\ I32.v x < 1000)
  returns r: I32.t
  ensures pure (I32.v r == I32.v x + 1)
{
  I32.add x 1l
}
""")]

namespace PalCSharp.Tests;

/// <summary>
/// A binder to a system the verifier cannot see -- here, standing in for a SQL statement --
/// tied to a verified model of it with <c>[Implements]</c>. Its translation is the call to
/// <c>CounterModel.bump</c>, so its contract is proved of the model function; its C# body
/// is trusted to do what the model does.
/// </summary>
public static class Counter
{
    [Implements("CounterModel.bump $(x)")]
    [Requires("0 <= x && x < 1000")]
    [Ensures("Result == x + 1")]
    public static int Bump(int x) => External.Increment(x);

    /// <summary>A verified client, relying only on the binder's (checked) contract.</summary>
    [Requires("0 <= x && x < 500")]
    [Ensures("Result == x + 2")]
    public static int BumpTwice(int x) => Bump(Bump(x));
}

/// <summary>The "external system": untranslated C#.</summary>
public static class External
{
    public static int Increment(int x) => x + 1;
}
