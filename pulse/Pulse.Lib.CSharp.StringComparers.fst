module Pulse.Lib.CSharp.StringComparers
#lang-pulse

open Pulse.Lib.Pervasives
module E = Pulse.Lib.CSharp.EqualityModel
module Raw = Pulse.Lib.CSharp.EqualityOpaque

fn randomized (c: E.handle)
requires pure (is_non_randomized c)
returns r: E.handle
ensures pure (randomized_from c r)
{
  let r = E.randomized c;
  assert (pure (randomized_from c r));
  r
}

let randomized_equals (#t: Type0) {| E.has_equality t |}
                      (c r: E.handle) (x y: t)
  : Lemma (requires randomized_from c r)
          (ensures E.equals r x y == E.equals c x y)
  = E.equals_definition c x y;
    E.equals_definition r x y
