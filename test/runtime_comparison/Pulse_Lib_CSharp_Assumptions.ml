(* Test-only realization of the existing trusted recovery interface.
   Custard erases Dyn to Obj.t; this adapter is not a proof of that axiom. *)
let recover x = Obj.obj x
