module Pulse.Lib.CSharp.RefJoin
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

#set-options "--z3rlimit 10"

// Keep the agreed fact inside the owned predicate while Pulse joins the arms.
// No mutable payload is pinned to its entry snapshot.
let framed (#a: Type0) (r: R.ref a) (p: perm) (fact: a -> prop) : slprop =
  exists* (v: a). R.pts_to r #p v ** pure (fact v)

ghost fn pack (#a: Type0) (r: R.ref a) (fact: a -> prop) (#v: erased a) (#p: perm)
  requires R.pts_to r #p v ** pure (fact (reveal v))
  ensures framed r p fact
{
  fold (framed r p fact);
}

ghost fn unpack (#a: Type0) (r: R.ref a) (fact: a -> prop) (#p: perm)
  requires framed r p fact
  ensures exists* (post: a). R.pts_to r #p post ** pure (fact post)
{
  unfold (framed r p fact);
}
