module Pulse.Lib.CSharp.Ownership

open Pulse.Lib.Pervasives

let require_erased (#a: Type0) (_: erased a -> Tot (erased a)) : Lemma True = ()

// The capabilities needed by object aliases. Unlike arbitrary fraction
// splitting, halving is provided by the public Box and Reference interfaces.
// Each user's instance is a pair of checked ghost programs, not an axiom.
[@@erasable]
class fractional (pred: perm -> slprop) = {
  share_half_op: (p: perm) -> unit ->
    stt_ghost unit emp_inames (pred p)
      (fun _ -> pred (p /. 2.0R) ** pred (p /. 2.0R));
  gather_op: (p: perm) -> (q: perm) -> unit ->
    stt_ghost unit emp_inames (pred p ** pred q)
      (fun _ -> pred (p +. q));
}

let share_half (#pred: perm -> slprop) {| f: fractional pred |} (p: perm) () =
  f.share_half_op p ()

let gather (#pred: perm -> slprop) {| f: fractional pred |} (p q: perm) () =
  f.gather_op p q ()
