// EXPECT-PULSE: I32.v _posth == I32.v var_x + 2’
// R20.14. An `[Implements]` binder's contract is proved of the Pulse it names, not assumed.
// `bump` returns its argument plus one; the binder claims plus two, which the model does
// not provide, so the binder itself is refused -- where `[Admit]` would have believed it.
using PalLang;

[assembly: IncludePulse("OverclaimModel", """
module OverclaimModel
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

public static class ImplementsOverclaims
{
    [Implements("OverclaimModel.bump $(x)")]
    [Requires("0 <= x && x < 1000")]
    [Ensures("Result == x + 2")]
    // MARKER
    public static int Bump(int x) => x + 2;
}
