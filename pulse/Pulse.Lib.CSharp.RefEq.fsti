module Pulse.Lib.CSharp.RefEq

module B = Pulse.Lib.Box

/// MODELING AXIOM (R27.8). Reference equality: C#'s `x == y` on two references of a class
/// with no `operator ==` compares the pointers, and that comparison decides equality of the
/// boxes that model them. It is the only fact about a box this axiom states.
val ref_eq (#a: Type0) (x y: B.box a) : b: bool { b <==> x == y }
