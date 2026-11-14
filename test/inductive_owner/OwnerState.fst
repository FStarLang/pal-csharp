module OwnerState

module I = FStar.Int32
open FStar.Ghost

let state = erased I.t
let make (x: I.t) : Tot state = hide x
let value (s: state) : GTot int = I.v (reveal s)
