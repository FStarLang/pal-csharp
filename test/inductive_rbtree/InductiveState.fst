module InductiveState

module C = InductiveCursor
module N = Class_RbNode
module D = Pulse.Lib.CSharp.TopDown
module M = InductiveMutation
open FStar.Ghost

// An erased value, rather than a live tree, is stored in PAL-only mutable
// locals. Operations accept erased snapshots without revealing into Tot data.
let state (a: Type0) = erased (C.tree a)
let labels (#a: Type0) (s: state a) : GTot (C.tree a) = reveal s
let start (#a: Type0) (s: erased (C.tree a)) : Tot (state a) = s
let recolor (#a: Type0) (s: state a) (x: N.class_RbNode__opt a) (red: bool) : Tot (state a) =
  hide (M.recolor (reveal s) x red)
let split (#a: Type0) (s: state a) (x: N.class_RbNode__opt a) : Tot (state a) =
  hide (InductiveInsert.split_tree (reveal s) x)
let balance (#a: Type0) (s: state a) (x: N.class_RbNode__opt a) : Tot (state a) =
  hide (D.balance (reveal s) x)
let black (#a: Type0) (s: state a) : Tot (state a) =
  hide (D.recolorn (reveal s) false)
let link (#a: Type0) (s: state a) (p x: N.class_RbNode__opt a) (k: a) (right: bool) : Tot (state a) =
  hide (D.set_child (reveal s) p right (D.leaf x k))
