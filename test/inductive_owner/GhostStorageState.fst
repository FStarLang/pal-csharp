module GhostStorageState

module I = FStar.Int32
open FStar.Ghost

let model (a: Type0) = list a & I.t
let state (a: Type0) = erased (model a)
let make (a: Type0) (x: I.t) : Tot (state a) = hide ([], x)
let value (#a: Type0) (s: state a) : GTot int = I.v (snd (reveal s))
let observe (#a: Type0) (s: state a) : GTot (model a) = reveal s
let model_value (#a: Type0) (m: model a) : Tot int = I.v (snd m)
