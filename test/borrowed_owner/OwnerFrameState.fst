module OwnerFrameState
open FStar.Ghost
let state = erased int
let make (n: FStar.Int32.t) : Tot state = hide (FStar.Int32.v n)
let next (s: state) : GTot state = hide (reveal s + 1)
