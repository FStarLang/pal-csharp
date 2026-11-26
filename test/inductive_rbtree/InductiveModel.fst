module InductiveModel

module T = Pulse.Lib.CSharp.Tree

let tree (a: Type0) = T.tree (a & bool)
let left (#a: Type0) (t: tree a) : tree a =
  match t with T.Leaf -> T.Leaf | T.Branch l _ _ -> l
let right (#a: Type0) (t: tree a) : tree a =
  match t with T.Leaf -> T.Leaf | T.Branch _ _ r -> r
let node (#a: Type0) (l: tree a) (k: a) (red: bool) (r: tree a) : tree a =
  T.Branch l (k, red) r
