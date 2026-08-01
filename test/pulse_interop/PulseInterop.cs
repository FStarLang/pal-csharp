using PalLang;

// Raw Pulse, carried into the translation as its own module. This is the escape
// hatch for definitions that have no C# surface at all -- here, a pure predicate
// stated directly over `FStar.Seq`.
[assembly: IncludePulse("MyPulse", """
module MyPulse
module Seq = FStar.Seq

let all_positive (s: Seq.seq FStar.Int32.t) : prop =
  forall (k: nat). k < Seq.length s ==> FStar.Int32.v (Seq.index s k) > 0

let all_positive_index (s: Seq.seq FStar.Int32.t) (k: nat)
  : Lemma (requires all_positive s /\ k < Seq.length s)
          (ensures FStar.Int32.v (Seq.index s k) > 0)
  = ()
""")]

namespace PalCSharp.Tests;

/// <summary>
/// Pulse interoperability: a module written in raw Pulse, referred to from C#
/// specifications through <c>Pal.InlinePulse</c>, with <c>$(...)</c> antiquotation
/// naming the translated form of a C# entity.
/// </summary>
public static class Positives
{
    [Requires("InlinePulse(\"MyPulse.all_positive $(a)\")")]
    [Requires("0 <= i && i < Contents(a).Length")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    [Ensures("Result > 0")]
    public static int PickPositive(int[] a, int i)
    {
        Pal.GhostStmt("MyPulse.all_positive_index $(a) (I32.v $(i))");
        return a[i];
    }
}
