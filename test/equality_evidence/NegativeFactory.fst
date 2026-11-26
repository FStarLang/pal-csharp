module NegativeFactory
#lang-pulse
open Pulse.Lib.Pervasives
module E = Pulse.Lib.CSharp.Equality
module SC = Pulse.Lib.CSharp.StringComparers

// Equality preservation does not identify the objects allocated by two calls.
fn incorrect (c: E.handle)
  requires pure (SC.is_non_randomized c)
  returns r: bool
  ensures pure r
{
  let a = SC.randomized c;
  let b = SC.randomized c;
  a = b
}
